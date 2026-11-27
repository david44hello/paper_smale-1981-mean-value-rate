/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover7_leaf0550; no trusted numerical premise.
theorem cover7_leaf0550_exp_radius : (249365659046102131/250000000000000000 : ℝ) ≤ Real.exp ((-333/16384 : ℝ)/8) ∧ Real.exp ((-333/16384 : ℝ)/8) ≤ (39898505447376341/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-333/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0550_exp_lower : (459046911797381183/500000000000000000 : ℝ) ≤ Real.exp ((-1367291027721/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367291027721/2000000000000 : ℝ)/8) ≤ (918093823594762367/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367291027721/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0550_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019093901691/1000000000000 : ℝ) ≤ 4*Real.exp (1165/8192 : ℝ)*Real.exp (-mu (radius 7 (2331/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019093901691/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2331/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0550_exp_radius
  have hrNumeric : (979880447573/1000000000000 : ℝ) ≤ Real.exp (-333/16384 : ℝ) ∧ Real.exp (-333/16384 : ℝ) ≤ (489940223787/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (979880447573/1000000000000 : ℝ) ≤ (radius 7 (2331/16384 : ℝ)) ∧ (radius 7 (2331/16384 : ℝ)) ≤ (489940223787/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2331/16384 : ℝ)) (979880447573/1000000000000 : ℝ) (489940223787/500000000000 : ℝ) (1995853413/10000000000 : ℝ) (99792670653/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2331/16384 : ℝ)) (979880447573/1000000000000 : ℝ) (489940223787/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2331/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (979880447573/1000000000000 : ℝ) (489940223787/500000000000 : ℝ) (494970111893/500000000000 : ℝ) (989940223787/1000000000000 : ℝ) (39595564349/40000000000 : ℝ) (494944554363/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2331/16384 : ℝ)) 1 (494970111893/500000000000 : ℝ) (989940223787/1000000000000 : ℝ) (39595564349/40000000000 : ℝ) (494944554363/500000000000 : ℝ) (197982933251/200000000000 : ℝ) (989914666257/1000000000000 : ℝ) (39596586637/40000000000 : ℝ) (989914665927/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2331/16384 : ℝ)) 2 (197982933251/200000000000 : ℝ) (989914666257/1000000000000 : ℝ) (39596586637/40000000000 : ℝ) (989914665927/1000000000000 : ℝ) (98991466609/100000000000 : ℝ) (247478666523/250000000000 : ℝ) (989914666089/1000000000000 : ℝ) (247478666523/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2331/16384 : ℝ)) 3 (98991466609/100000000000 : ℝ) (247478666523/250000000000 : ℝ) (989914666089/1000000000000 : ℝ) (247478666523/250000000000 : ℝ) (989914666089/1000000000000 : ℝ) (247478666523/250000000000 : ℝ) (989914666089/1000000000000 : ℝ) (247478666523/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2331/16384 : ℝ)) 4 (989914666089/1000000000000 : ℝ) (247478666523/250000000000 : ℝ) (989914666089/1000000000000 : ℝ) (247478666523/250000000000 : ℝ) (989914666089/1000000000000 : ℝ) (247478666523/250000000000 : ℝ) (989914666089/1000000000000 : ℝ) (247478666523/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2331/16384 : ℝ)) 5 (989914666089/1000000000000 : ℝ) (247478666523/250000000000 : ℝ) (989914666089/1000000000000 : ℝ) (247478666523/250000000000 : ℝ) (989914666089/1000000000000 : ℝ) (247478666523/250000000000 : ℝ) (989914666089/1000000000000 : ℝ) (247478666523/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2331/16384 : ℝ)) 6 (989914666089/1000000000000 : ℝ) (247478666523/250000000000 : ℝ) (989914666089/1000000000000 : ℝ) (247478666523/250000000000 : ℝ) (989914666089/1000000000000 : ℝ) (247478666523/250000000000 : ℝ) (989914666089/1000000000000 : ℝ) (247478666523/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2331/16384 : ℝ)) 7 (989914666089/1000000000000 : ℝ) (247478666523/250000000000 : ℝ) (989914666089/1000000000000 : ℝ) (247478666523/250000000000 : ℝ) (989914666089/1000000000000 : ℝ) (247478666523/250000000000 : ℝ) (989914666089/1000000000000 : ℝ) (247478666523/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2331/16384 : ℝ))) (1995853413/10000000000 : ℝ) (99792670653/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2331/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (1995853413/10000000000 : ℝ) (99792670653/500000000000 : ℝ) (11995853413/20000000000 : ℝ) (599792670653/1000000000000 : ℝ) (223374876217/500000000000 : ℝ) (446749752441/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2331/16384 : ℝ))) 1 (11995853413/20000000000 : ℝ) (599792670653/1000000000000 : ℝ) (223374876217/500000000000 : ℝ) (446749752441/1000000000000 : ℝ) (261635605771/500000000000 : ℝ) (523271211547/1000000000000 : ℝ) (64705731383/125000000000 : ℝ) (517645851071/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2331/16384 : ℝ))) 2 (261635605771/500000000000 : ℝ) (523271211547/1000000000000 : ℝ) (64705731383/125000000000 : ℝ) (517645851071/1000000000000 : ℝ) (520458531303/1000000000000 : ℝ) (520458531309/1000000000000 : ℝ) (260225465527/500000000000 : ℝ) (520450931061/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2331/16384 : ℝ))) 3 (520458531303/1000000000000 : ℝ) (520458531309/1000000000000 : ℝ) (260225465527/500000000000 : ℝ) (520450931061/1000000000000 : ℝ) (260227365589/500000000000 : ℝ) (104090946237/200000000000 : ℝ) (130113682791/250000000000 : ℝ) (130113682793/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2331/16384 : ℝ))) 4 (260227365589/500000000000 : ℝ) (104090946237/200000000000 : ℝ) (130113682791/250000000000 : ℝ) (130113682793/250000000000 : ℝ) (520454731171/1000000000000 : ℝ) (520454731179/1000000000000 : ℝ) (52045473117/100000000000 : ℝ) (520454731179/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2331/16384 : ℝ))) 5 (520454731171/1000000000000 : ℝ) (520454731179/1000000000000 : ℝ) (52045473117/100000000000 : ℝ) (520454731179/1000000000000 : ℝ) (52045473117/100000000000 : ℝ) (520454731179/1000000000000 : ℝ) (52045473117/100000000000 : ℝ) (520454731179/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2331/16384 : ℝ))) 6 (52045473117/100000000000 : ℝ) (520454731179/1000000000000 : ℝ) (52045473117/100000000000 : ℝ) (520454731179/1000000000000 : ℝ) (52045473117/100000000000 : ℝ) (520454731179/1000000000000 : ℝ) (52045473117/100000000000 : ℝ) (520454731179/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2331/16384 : ℝ))) 7 (52045473117/100000000000 : ℝ) (520454731179/1000000000000 : ℝ) (52045473117/100000000000 : ℝ) (520454731179/1000000000000 : ℝ) (52045473117/100000000000 : ℝ) (520454731179/1000000000000 : ℝ) (52045473117/100000000000 : ℝ) (520454731179/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2331/16384 : ℝ)) hmem 8 (989914666089/1000000000000 : ℝ) (247478666523/250000000000 : ℝ) (989914666089/1000000000000 : ℝ) (247478666523/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2331/16384 : ℝ))) hcmem 8 (52045473117/100000000000 : ℝ) (520454731179/1000000000000 : ℝ) (52045473117/100000000000 : ℝ) (520454731179/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2331/16384 : ℝ)) (989914666089/1000000000000 : ℝ) (247478666523/250000000000 : ℝ) (52045473117/100000000000 : ℝ) (520454731179/1000000000000 : ℝ) (165171485581/200000000000 : ℝ) (825857427923/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0550_exp_lower
  have heNumeric : (2019093901691/1000000000000 : ℝ)/4 ≤ Real.exp (-1367291027721/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019093901691/1000000000000 : ℝ)/4 ≤ Real.exp ((1165/8192 : ℝ)-(825857427923/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1165/8192 : ℝ) (2331/16384 : ℝ) (825857427923/1000000000000 : ℝ) (2019093901691/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0551; no trusted numerical premise.
theorem cover7_leaf0551_exp_radius : (249365387259250899/250000000000000000 : ℝ) ≤ Real.exp ((-583/28672 : ℝ)/8) ∧ Real.exp ((-583/28672 : ℝ)/8) ≤ (997461549037003597/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-583/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0551_exp_lower : (918094024698559909/1000000000000000000 : ℝ) ≤ Real.exp ((-546915009201/800000000000 : ℝ)/8) ∧ Real.exp ((-546915009201/800000000000 : ℝ)/8) ≤ (91809402469855991/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-546915009201/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0551_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (15774198749/7812500000 : ℝ) ≤ 4*Real.exp (2331/16384 : ℝ)*Real.exp (-mu (radius 7 (583/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (15774198749/7812500000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (583/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0551_exp_radius
  have hrNumeric : (979871903731/1000000000000 : ℝ) ≤ Real.exp (-583/28672 : ℝ) ∧ Real.exp (-583/28672 : ℝ) ≤ (244967975933/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (979871903731/1000000000000 : ℝ) ≤ (radius 7 (583/4096 : ℝ)) ∧ (radius 7 (583/4096 : ℝ)) ≤ (244967975933/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (583/4096 : ℝ)) (979871903731/1000000000000 : ℝ) (244967975933/250000000000 : ℝ) (199627283397/1000000000000 : ℝ) (199627283403/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (583/4096 : ℝ)) (979871903731/1000000000000 : ℝ) (244967975933/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (583/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (979871903731/1000000000000 : ℝ) (244967975933/250000000000 : ℝ) (197987190373/200000000000 : ℝ) (494967975933/500000000000 : ℝ) (24747119829/25000000000 : ℝ) (494942396581/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (583/4096 : ℝ)) 1 (197987190373/200000000000 : ℝ) (494967975933/500000000000 : ℝ) (24747119829/25000000000 : ℝ) (494942396581/500000000000 : ℝ) (30934699141/31250000000 : ℝ) (494955186257/500000000000 : ℝ) (494955186091/500000000000 : ℝ) (123738796523/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (583/4096 : ℝ)) 2 (30934699141/31250000000 : ℝ) (494955186257/500000000000 : ℝ) (494955186091/500000000000 : ℝ) (123738796523/125000000000 : ℝ) (989910372347/1000000000000 : ℝ) (989910372349/1000000000000 : ℝ) (494955186173/500000000000 : ℝ) (989910372349/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (583/4096 : ℝ)) 3 (989910372347/1000000000000 : ℝ) (989910372349/1000000000000 : ℝ) (494955186173/500000000000 : ℝ) (989910372349/1000000000000 : ℝ) (494955186173/500000000000 : ℝ) (989910372349/1000000000000 : ℝ) (494955186173/500000000000 : ℝ) (989910372349/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (583/4096 : ℝ)) 4 (494955186173/500000000000 : ℝ) (989910372349/1000000000000 : ℝ) (494955186173/500000000000 : ℝ) (989910372349/1000000000000 : ℝ) (494955186173/500000000000 : ℝ) (989910372349/1000000000000 : ℝ) (494955186173/500000000000 : ℝ) (989910372349/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (583/4096 : ℝ)) 5 (494955186173/500000000000 : ℝ) (989910372349/1000000000000 : ℝ) (494955186173/500000000000 : ℝ) (989910372349/1000000000000 : ℝ) (494955186173/500000000000 : ℝ) (989910372349/1000000000000 : ℝ) (494955186173/500000000000 : ℝ) (989910372349/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (583/4096 : ℝ)) 6 (494955186173/500000000000 : ℝ) (989910372349/1000000000000 : ℝ) (494955186173/500000000000 : ℝ) (989910372349/1000000000000 : ℝ) (494955186173/500000000000 : ℝ) (989910372349/1000000000000 : ℝ) (494955186173/500000000000 : ℝ) (989910372349/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (583/4096 : ℝ)) 7 (494955186173/500000000000 : ℝ) (989910372349/1000000000000 : ℝ) (494955186173/500000000000 : ℝ) (989910372349/1000000000000 : ℝ) (494955186173/500000000000 : ℝ) (989910372349/1000000000000 : ℝ) (494955186173/500000000000 : ℝ) (989910372349/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (583/4096 : ℝ))) (199627283397/1000000000000 : ℝ) (199627283403/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (583/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (199627283397/1000000000000 : ℝ) (199627283403/1000000000000 : ℝ) (299906820849/500000000000 : ℝ) (299906820851/500000000000 : ℝ) (89359338269/200000000000 : ℝ) (55849586419/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (583/4096 : ℝ))) 1 (299906820849/500000000000 : ℝ) (299906820851/500000000000 : ℝ) (89359338269/200000000000 : ℝ) (55849586419/125000000000 : ℝ) (523305166521/1000000000000 : ℝ) (523305166527/1000000000000 : ℝ) (517682094083/1000000000000 : ℝ) (517682094089/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (583/4096 : ℝ))) 2 (523305166521/1000000000000 : ℝ) (523305166527/1000000000000 : ℝ) (517682094083/1000000000000 : ℝ) (517682094089/1000000000000 : ℝ) (260246815151/500000000000 : ℝ) (130123407577/250000000000 : ℝ) (520486036747/1000000000000 : ℝ) (260243018377/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (583/4096 : ℝ))) 3 (260246815151/500000000000 : ℝ) (130123407577/250000000000 : ℝ) (520486036747/1000000000000 : ℝ) (260243018377/500000000000 : ℝ) (130122458381/250000000000 : ℝ) (520489833531/1000000000000 : ℝ) (52048983351/100000000000 : ℝ) (260244916759/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (583/4096 : ℝ))) 4 (130122458381/250000000000 : ℝ) (520489833531/1000000000000 : ℝ) (52048983351/100000000000 : ℝ) (260244916759/500000000000 : ℝ) (520489833517/1000000000000 : ℝ) (20819593341/40000000000 : ℝ) (130122458379/250000000000 : ℝ) (20819593341/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (583/4096 : ℝ))) 5 (520489833517/1000000000000 : ℝ) (20819593341/40000000000 : ℝ) (130122458379/250000000000 : ℝ) (20819593341/40000000000 : ℝ) (130122458379/250000000000 : ℝ) (20819593341/40000000000 : ℝ) (130122458379/250000000000 : ℝ) (20819593341/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (583/4096 : ℝ))) 6 (130122458379/250000000000 : ℝ) (20819593341/40000000000 : ℝ) (130122458379/250000000000 : ℝ) (20819593341/40000000000 : ℝ) (130122458379/250000000000 : ℝ) (20819593341/40000000000 : ℝ) (130122458379/250000000000 : ℝ) (20819593341/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (583/4096 : ℝ))) 7 (130122458379/250000000000 : ℝ) (20819593341/40000000000 : ℝ) (130122458379/250000000000 : ℝ) (20819593341/40000000000 : ℝ) (130122458379/250000000000 : ℝ) (20819593341/40000000000 : ℝ) (130122458379/250000000000 : ℝ) (20819593341/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (583/4096 : ℝ)) hmem 8 (494955186173/500000000000 : ℝ) (989910372349/1000000000000 : ℝ) (494955186173/500000000000 : ℝ) (989910372349/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (583/4096 : ℝ))) hcmem 8 (130122458379/250000000000 : ℝ) (20819593341/40000000000 : ℝ) (130122458379/250000000000 : ℝ) (20819593341/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (583/4096 : ℝ)) (494955186173/500000000000 : ℝ) (989910372349/1000000000000 : ℝ) (130122458379/250000000000 : ℝ) (20819593341/40000000000 : ℝ) (412958355351/500000000000 : ℝ) (2580989721/3125000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0551_exp_lower
  have heNumeric : (15774198749/7812500000 : ℝ)/4 ≤ Real.exp (-546915009201/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (15774198749/7812500000 : ℝ)/4 ≤ Real.exp ((2331/16384 : ℝ)-(2580989721/3125000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2331/16384 : ℝ) (583/4096 : ℝ) (2580989721/3125000000 : ℝ) (15774198749/7812500000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0552; no trusted numerical premise.
theorem cover7_leaf0552_exp_radius : (199492092378156713/200000000000000000 : ℝ) ≤ Real.exp ((-2333/114688 : ℝ)/8) ∧ Real.exp ((-2333/114688 : ℝ)/8) ≤ (498730230945391783/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2333/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0552_exp_lower : (918094227742793651/1000000000000000000 : ℝ) ≤ Real.exp ((-341820996117/500000000000 : ℝ)/8) ∧ Real.exp ((-341820996117/500000000000 : ℝ)/8) ≤ (229523556935698413/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341820996117/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0552_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009550506099/500000000000 : ℝ) ≤ 4*Real.exp (583/4096 : ℝ)*Real.exp (-mu (radius 7 (2333/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (1009550506099/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2333/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0552_exp_radius
  have hrNumeric : (979863359963/1000000000000 : ℝ) ≤ Real.exp (-2333/114688 : ℝ) ∧ Real.exp (-2333/114688 : ℝ) ≤ (244965839991/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (979863359963/1000000000000 : ℝ) ≤ (radius 7 (2333/16384 : ℝ)) ∧ (radius 7 (2333/16384 : ℝ)) ≤ (244965839991/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2333/16384 : ℝ)) (979863359963/1000000000000 : ℝ) (244965839991/250000000000 : ℝ) (99834607977/500000000000 : ℝ) (4991730399/25000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2333/16384 : ℝ)) (979863359963/1000000000000 : ℝ) (244965839991/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2333/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (979863359963/1000000000000 : ℝ) (244965839991/250000000000 : ℝ) (989931679981/1000000000000 : ℝ) (494965839991/500000000000 : ℝ) (494940238807/500000000000 : ℝ) (61867529851/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2333/16384 : ℝ)) 1 (989931679981/1000000000000 : ℝ) (494965839991/500000000000 : ℝ) (494940238807/500000000000 : ℝ) (61867529851/62500000000 : ℝ) (989906078797/1000000000000 : ℝ) (989906078799/1000000000000 : ℝ) (494953039233/500000000000 : ℝ) (247476519617/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2333/16384 : ℝ)) 2 (989906078797/1000000000000 : ℝ) (989906078799/1000000000000 : ℝ) (494953039233/500000000000 : ℝ) (247476519617/250000000000 : ℝ) (989906078631/1000000000000 : ℝ) (494953039317/500000000000 : ℝ) (989906078631/1000000000000 : ℝ) (494953039317/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2333/16384 : ℝ)) 3 (989906078631/1000000000000 : ℝ) (494953039317/500000000000 : ℝ) (989906078631/1000000000000 : ℝ) (494953039317/500000000000 : ℝ) (989906078631/1000000000000 : ℝ) (494953039317/500000000000 : ℝ) (989906078631/1000000000000 : ℝ) (494953039317/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2333/16384 : ℝ)) 4 (989906078631/1000000000000 : ℝ) (494953039317/500000000000 : ℝ) (989906078631/1000000000000 : ℝ) (494953039317/500000000000 : ℝ) (989906078631/1000000000000 : ℝ) (494953039317/500000000000 : ℝ) (989906078631/1000000000000 : ℝ) (494953039317/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2333/16384 : ℝ)) 5 (989906078631/1000000000000 : ℝ) (494953039317/500000000000 : ℝ) (989906078631/1000000000000 : ℝ) (494953039317/500000000000 : ℝ) (989906078631/1000000000000 : ℝ) (494953039317/500000000000 : ℝ) (989906078631/1000000000000 : ℝ) (494953039317/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2333/16384 : ℝ)) 6 (989906078631/1000000000000 : ℝ) (494953039317/500000000000 : ℝ) (989906078631/1000000000000 : ℝ) (494953039317/500000000000 : ℝ) (989906078631/1000000000000 : ℝ) (494953039317/500000000000 : ℝ) (989906078631/1000000000000 : ℝ) (494953039317/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2333/16384 : ℝ)) 7 (989906078631/1000000000000 : ℝ) (494953039317/500000000000 : ℝ) (989906078631/1000000000000 : ℝ) (494953039317/500000000000 : ℝ) (989906078631/1000000000000 : ℝ) (494953039317/500000000000 : ℝ) (989906078631/1000000000000 : ℝ) (494953039317/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2333/16384 : ℝ))) (99834607977/500000000000 : ℝ) (4991730399/25000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2333/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (99834607977/500000000000 : ℝ) (4991730399/25000000000 : ℝ) (599834607977/1000000000000 : ℝ) (29991730399/50000000000 : ℝ) (8936872293/20000000000 : ℝ) (223421807329/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2333/16384 : ℝ))) 1 (599834607977/1000000000000 : ℝ) (29991730399/50000000000 : ℝ) (8936872293/20000000000 : ℝ) (223421807329/500000000000 : ℝ) (523339111313/1000000000000 : ℝ) (523339111319/1000000000000 : ℝ) (258859162683/500000000000 : ℝ) (517718325373/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2333/16384 : ℝ))) 2 (523339111313/1000000000000 : ℝ) (523339111319/1000000000000 : ℝ) (258859162683/500000000000 : ℝ) (517718325373/1000000000000 : ℝ) (520528718339/1000000000000 : ℝ) (260264359173/500000000000 : ℝ) (52052113147/100000000000 : ℝ) (260260565739/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2333/16384 : ℝ))) 3 (520528718339/1000000000000 : ℝ) (260264359173/500000000000 : ℝ) (52052113147/100000000000 : ℝ) (260260565739/500000000000 : ℝ) (65065615613/125000000000 : ℝ) (32532807807/62500000000 : ℝ) (52052492489/100000000000 : ℝ) (520524924899/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2333/16384 : ℝ))) 4 (65065615613/125000000000 : ℝ) (32532807807/62500000000 : ℝ) (52052492489/100000000000 : ℝ) (520524924899/1000000000000 : ℝ) (520524924897/1000000000000 : ℝ) (260262462453/500000000000 : ℝ) (16266403903/31250000000 : ℝ) (260262462453/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2333/16384 : ℝ))) 5 (520524924897/1000000000000 : ℝ) (260262462453/500000000000 : ℝ) (16266403903/31250000000 : ℝ) (260262462453/500000000000 : ℝ) (16266403903/31250000000 : ℝ) (260262462453/500000000000 : ℝ) (16266403903/31250000000 : ℝ) (260262462453/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2333/16384 : ℝ))) 6 (16266403903/31250000000 : ℝ) (260262462453/500000000000 : ℝ) (16266403903/31250000000 : ℝ) (260262462453/500000000000 : ℝ) (16266403903/31250000000 : ℝ) (260262462453/500000000000 : ℝ) (16266403903/31250000000 : ℝ) (260262462453/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2333/16384 : ℝ))) 7 (16266403903/31250000000 : ℝ) (260262462453/500000000000 : ℝ) (16266403903/31250000000 : ℝ) (260262462453/500000000000 : ℝ) (16266403903/31250000000 : ℝ) (260262462453/500000000000 : ℝ) (16266403903/31250000000 : ℝ) (260262462453/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2333/16384 : ℝ)) hmem 8 (989906078631/1000000000000 : ℝ) (494953039317/500000000000 : ℝ) (989906078631/1000000000000 : ℝ) (494953039317/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2333/16384 : ℝ))) hcmem 8 (16266403903/31250000000 : ℝ) (260262462453/500000000000 : ℝ) (16266403903/31250000000 : ℝ) (260262462453/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2333/16384 : ℝ)) (989906078631/1000000000000 : ℝ) (494953039317/500000000000 : ℝ) (16266403903/31250000000 : ℝ) (260262462453/500000000000 : ℝ) (825975976589/1000000000000 : ℝ) (825975976609/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0552_exp_lower
  have heNumeric : (1009550506099/500000000000 : ℝ)/4 ≤ Real.exp (-341820996117/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009550506099/500000000000 : ℝ)/4 ≤ Real.exp ((583/4096 : ℝ)-(825975976609/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (583/4096 : ℝ) (2333/16384 : ℝ) (825975976609/1000000000000 : ℝ) (1009550506099/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0553; no trusted numerical premise.
theorem cover7_leaf0553_exp_radius : (249364843686437107/250000000000000000 : ℝ) ≤ Real.exp ((-1167/57344 : ℝ)/8) ∧ Real.exp ((-1167/57344 : ℝ)/8) ≤ (997459374745748429/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1167/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0553_exp_lower : (91809443272677631/100000000000000000 : ℝ) ≤ Real.exp ((-2734560824259/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734560824259/4000000000000 : ℝ)/8) ≤ (918094432726776311/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734560824259/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0553_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009552309329/500000000000 : ℝ) ≤ 4*Real.exp (2333/16384 : ℝ)*Real.exp (-mu (radius 7 (1167/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (1009552309329/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1167/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0553_exp_radius
  have hrNumeric : (97985481627/100000000000 : ℝ) ≤ Real.exp (-1167/57344 : ℝ) ∧ Real.exp (-1167/57344 : ℝ) ≤ (979854816271/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (97985481627/100000000000 : ℝ) ≤ (radius 7 (1167/8192 : ℝ)) ∧ (radius 7 (1167/8192 : ℝ)) ≤ (979854816271/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1167/8192 : ℝ)) (97985481627/100000000000 : ℝ) (979854816271/1000000000000 : ℝ) (99855569487/500000000000 : ℝ) (9985556949/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1167/8192 : ℝ)) (97985481627/100000000000 : ℝ) (979854816271/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1167/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (97985481627/100000000000 : ℝ) (979854816271/1000000000000 : ℝ) (197985481627/200000000000 : ℝ) (123740926017/125000000000 : ℝ) (989876162087/1000000000000 : ℝ) (989876162089/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1167/8192 : ℝ)) 1 (197985481627/200000000000 : ℝ) (123740926017/125000000000 : ℝ) (989876162087/1000000000000 : ℝ) (989876162089/1000000000000 : ℝ) (989901785111/1000000000000 : ℝ) (989901785113/1000000000000 : ℝ) (989901784779/1000000000000 : ℝ) (989901784781/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1167/8192 : ℝ)) 2 (989901785111/1000000000000 : ℝ) (989901785113/1000000000000 : ℝ) (989901784779/1000000000000 : ℝ) (989901784781/1000000000000 : ℝ) (197980356989/200000000000 : ℝ) (989901784947/1000000000000 : ℝ) (61868861559/62500000000 : ℝ) (989901784947/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1167/8192 : ℝ)) 3 (197980356989/200000000000 : ℝ) (989901784947/1000000000000 : ℝ) (61868861559/62500000000 : ℝ) (989901784947/1000000000000 : ℝ) (61868861559/62500000000 : ℝ) (989901784947/1000000000000 : ℝ) (61868861559/62500000000 : ℝ) (989901784947/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1167/8192 : ℝ)) 4 (61868861559/62500000000 : ℝ) (989901784947/1000000000000 : ℝ) (61868861559/62500000000 : ℝ) (989901784947/1000000000000 : ℝ) (61868861559/62500000000 : ℝ) (989901784947/1000000000000 : ℝ) (61868861559/62500000000 : ℝ) (989901784947/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1167/8192 : ℝ)) 5 (61868861559/62500000000 : ℝ) (989901784947/1000000000000 : ℝ) (61868861559/62500000000 : ℝ) (989901784947/1000000000000 : ℝ) (61868861559/62500000000 : ℝ) (989901784947/1000000000000 : ℝ) (61868861559/62500000000 : ℝ) (989901784947/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1167/8192 : ℝ)) 6 (61868861559/62500000000 : ℝ) (989901784947/1000000000000 : ℝ) (61868861559/62500000000 : ℝ) (989901784947/1000000000000 : ℝ) (61868861559/62500000000 : ℝ) (989901784947/1000000000000 : ℝ) (61868861559/62500000000 : ℝ) (989901784947/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1167/8192 : ℝ)) 7 (61868861559/62500000000 : ℝ) (989901784947/1000000000000 : ℝ) (61868861559/62500000000 : ℝ) (989901784947/1000000000000 : ℝ) (61868861559/62500000000 : ℝ) (989901784947/1000000000000 : ℝ) (61868861559/62500000000 : ℝ) (989901784947/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1167/8192 : ℝ))) (99855569487/500000000000 : ℝ) (9985556949/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1167/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (99855569487/500000000000 : ℝ) (9985556949/50000000000 : ℝ) (599855569487/1000000000000 : ℝ) (59985556949/100000000000 : ℝ) (223445261179/500000000000 : ℝ) (223445261183/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1167/8192 : ℝ))) 1 (599855569487/1000000000000 : ℝ) (59985556949/100000000000 : ℝ) (223445261179/500000000000 : ℝ) (223445261183/500000000000 : ℝ) (261686522961/500000000000 : ℝ) (65421630741/125000000000 : ℝ) (258877272461/500000000000 : ℝ) (16179829529/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1167/8192 : ℝ))) 2 (261686522961/500000000000 : ℝ) (65421630741/125000000000 : ℝ) (258877272461/500000000000 : ℝ) (16179829529/31250000000 : ℝ) (260281897711/500000000000 : ℝ) (130140948857/250000000000 : ℝ) (520556215231/1000000000000 : ℝ) (260278107619/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1167/8192 : ℝ))) 3 (260281897711/500000000000 : ℝ) (130140948857/250000000000 : ℝ) (520556215231/1000000000000 : ℝ) (260278107619/500000000000 : ℝ) (260280002663/500000000000 : ℝ) (520560005333/1000000000000 : ℝ) (8133750083/15625000000 : ℝ) (13014000133/25000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1167/8192 : ℝ))) 4 (260280002663/500000000000 : ℝ) (520560005333/1000000000000 : ℝ) (8133750083/15625000000 : ℝ) (13014000133/25000000000 : ℝ) (520560005319/1000000000000 : ℝ) (520560005327/1000000000000 : ℝ) (260280002659/500000000000 : ℝ) (520560005327/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1167/8192 : ℝ))) 5 (520560005319/1000000000000 : ℝ) (520560005327/1000000000000 : ℝ) (260280002659/500000000000 : ℝ) (520560005327/1000000000000 : ℝ) (260280002659/500000000000 : ℝ) (520560005327/1000000000000 : ℝ) (260280002659/500000000000 : ℝ) (520560005327/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1167/8192 : ℝ))) 6 (260280002659/500000000000 : ℝ) (520560005327/1000000000000 : ℝ) (260280002659/500000000000 : ℝ) (520560005327/1000000000000 : ℝ) (260280002659/500000000000 : ℝ) (520560005327/1000000000000 : ℝ) (260280002659/500000000000 : ℝ) (520560005327/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1167/8192 : ℝ))) 7 (260280002659/500000000000 : ℝ) (520560005327/1000000000000 : ℝ) (260280002659/500000000000 : ℝ) (520560005327/1000000000000 : ℝ) (260280002659/500000000000 : ℝ) (520560005327/1000000000000 : ℝ) (260280002659/500000000000 : ℝ) (520560005327/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1167/8192 : ℝ)) hmem 8 (61868861559/62500000000 : ℝ) (989901784947/1000000000000 : ℝ) (61868861559/62500000000 : ℝ) (989901784947/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1167/8192 : ℝ))) hcmem 8 (260280002659/500000000000 : ℝ) (520560005327/1000000000000 : ℝ) (260280002659/500000000000 : ℝ) (520560005327/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1167/8192 : ℝ)) (61868861559/62500000000 : ℝ) (989901784947/1000000000000 : ℝ) (260280002659/500000000000 : ℝ) (520560005327/1000000000000 : ℝ) (826035225579/1000000000000 : ℝ) (206508806399/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0553_exp_lower
  have heNumeric : (1009552309329/500000000000 : ℝ)/4 ≤ Real.exp (-2734560824259/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009552309329/500000000000 : ℝ)/4 ≤ Real.exp ((2333/16384 : ℝ)-(206508806399/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2333/16384 : ℝ) (1167/8192 : ℝ) (206508806399/250000000000 : ℝ) (1009552309329/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0554; no trusted numerical premise.
theorem cover7_leaf0554_exp_radius : (199491657520379637/200000000000000000 : ℝ) ≤ Real.exp ((-2335/114688 : ℝ)/8) ∧ Real.exp ((-2335/114688 : ℝ)/8) ≤ (498729143800949093/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2335/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0554_exp_lower : (57380914978006199/62500000000000000 : ℝ) ≤ Real.exp ((-1367276806029/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367276806029/2000000000000 : ℝ)/8) ≤ (183618927929619837/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367276806029/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0554_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252388532401/125000000000 : ℝ) ≤ 4*Real.exp (1167/8192 : ℝ)*Real.exp (-mu (radius 7 (2335/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (252388532401/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2335/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0554_exp_radius
  have hrNumeric : (979846272651/1000000000000 : ℝ) ≤ Real.exp (-2335/114688 : ℝ) ∧ Real.exp (-2335/114688 : ℝ) ≤ (244961568163/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (979846272651/1000000000000 : ℝ) ≤ (radius 7 (2335/16384 : ℝ)) ∧ (radius 7 (2335/16384 : ℝ)) ≤ (244961568163/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2335/16384 : ℝ)) (979846272651/1000000000000 : ℝ) (244961568163/250000000000 : ℝ) (199753052467/1000000000000 : ℝ) (199753052473/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2335/16384 : ℝ)) (979846272651/1000000000000 : ℝ) (244961568163/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2335/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (979846272651/1000000000000 : ℝ) (244961568163/250000000000 : ℝ) (39596925453/40000000000 : ℝ) (494961568163/500000000000 : ℝ) (989871846579/1000000000000 : ℝ) (989871846581/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2335/16384 : ℝ)) 1 (39596925453/40000000000 : ℝ) (494961568163/500000000000 : ℝ) (989871846579/1000000000000 : ℝ) (989871846581/1000000000000 : ℝ) (247474372863/250000000000 : ℝ) (494948745727/500000000000 : ℝ) (989897491119/1000000000000 : ℝ) (494948745561/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2335/16384 : ℝ)) 2 (247474372863/250000000000 : ℝ) (494948745727/500000000000 : ℝ) (989897491119/1000000000000 : ℝ) (494948745561/500000000000 : ℝ) (197979498257/200000000000 : ℝ) (123737186411/125000000000 : ℝ) (197979498257/200000000000 : ℝ) (123737186411/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2335/16384 : ℝ)) 3 (197979498257/200000000000 : ℝ) (123737186411/125000000000 : ℝ) (197979498257/200000000000 : ℝ) (123737186411/125000000000 : ℝ) (197979498257/200000000000 : ℝ) (123737186411/125000000000 : ℝ) (197979498257/200000000000 : ℝ) (123737186411/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2335/16384 : ℝ)) 4 (197979498257/200000000000 : ℝ) (123737186411/125000000000 : ℝ) (197979498257/200000000000 : ℝ) (123737186411/125000000000 : ℝ) (197979498257/200000000000 : ℝ) (123737186411/125000000000 : ℝ) (197979498257/200000000000 : ℝ) (123737186411/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2335/16384 : ℝ)) 5 (197979498257/200000000000 : ℝ) (123737186411/125000000000 : ℝ) (197979498257/200000000000 : ℝ) (123737186411/125000000000 : ℝ) (197979498257/200000000000 : ℝ) (123737186411/125000000000 : ℝ) (197979498257/200000000000 : ℝ) (123737186411/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2335/16384 : ℝ)) 6 (197979498257/200000000000 : ℝ) (123737186411/125000000000 : ℝ) (197979498257/200000000000 : ℝ) (123737186411/125000000000 : ℝ) (197979498257/200000000000 : ℝ) (123737186411/125000000000 : ℝ) (197979498257/200000000000 : ℝ) (123737186411/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2335/16384 : ℝ)) 7 (197979498257/200000000000 : ℝ) (123737186411/125000000000 : ℝ) (197979498257/200000000000 : ℝ) (123737186411/125000000000 : ℝ) (197979498257/200000000000 : ℝ) (123737186411/125000000000 : ℝ) (197979498257/200000000000 : ℝ) (123737186411/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2335/16384 : ℝ))) (199753052467/1000000000000 : ℝ) (199753052473/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2335/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (199753052467/1000000000000 : ℝ) (199753052473/1000000000000 : ℝ) (599876526233/1000000000000 : ℝ) (599876526237/1000000000000 : ℝ) (89387482897/200000000000 : ℝ) (446937414493/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2335/16384 : ℝ))) 1 (599876526233/1000000000000 : ℝ) (599876526237/1000000000000 : ℝ) (89387482897/200000000000 : ℝ) (446937414493/1000000000000 : ℝ) (523406970359/1000000000000 : ℝ) (104681394073/200000000000 : ℝ) (517790752761/1000000000000 : ℝ) (126413758/244140625 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2335/16384 : ℝ))) 2 (523406970359/1000000000000 : ℝ) (104681394073/200000000000 : ℝ) (517790752761/1000000000000 : ℝ) (126413758/244140625 : ℝ) (13014971539/25000000000 : ℝ) (520598861567/1000000000000 : ℝ) (520591288039/1000000000000 : ℝ) (260295644023/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2335/16384 : ℝ))) 3 (13014971539/25000000000 : ℝ) (520598861567/1000000000000 : ℝ) (520591288039/1000000000000 : ℝ) (260295644023/500000000000 : ℝ) (520595074799/1000000000000 : ℝ) (520595074807/1000000000000 : ℝ) (104119014957/200000000000 : ℝ) (520595074793/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2335/16384 : ℝ))) 4 (520595074799/1000000000000 : ℝ) (520595074807/1000000000000 : ℝ) (104119014957/200000000000 : ℝ) (520595074793/1000000000000 : ℝ) (65074384349/125000000000 : ℝ) (1301487687/2500000000 : ℝ) (520595074791/1000000000000 : ℝ) (1301487687/2500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2335/16384 : ℝ))) 5 (65074384349/125000000000 : ℝ) (1301487687/2500000000 : ℝ) (520595074791/1000000000000 : ℝ) (1301487687/2500000000 : ℝ) (520595074791/1000000000000 : ℝ) (1301487687/2500000000 : ℝ) (520595074791/1000000000000 : ℝ) (1301487687/2500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2335/16384 : ℝ))) 6 (520595074791/1000000000000 : ℝ) (1301487687/2500000000 : ℝ) (520595074791/1000000000000 : ℝ) (1301487687/2500000000 : ℝ) (520595074791/1000000000000 : ℝ) (1301487687/2500000000 : ℝ) (520595074791/1000000000000 : ℝ) (1301487687/2500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2335/16384 : ℝ))) 7 (520595074791/1000000000000 : ℝ) (1301487687/2500000000 : ℝ) (520595074791/1000000000000 : ℝ) (1301487687/2500000000 : ℝ) (520595074791/1000000000000 : ℝ) (1301487687/2500000000 : ℝ) (520595074791/1000000000000 : ℝ) (1301487687/2500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2335/16384 : ℝ)) hmem 8 (197979498257/200000000000 : ℝ) (123737186411/125000000000 : ℝ) (197979498257/200000000000 : ℝ) (123737186411/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2335/16384 : ℝ))) hcmem 8 (520595074791/1000000000000 : ℝ) (1301487687/2500000000 : ℝ) (520595074791/1000000000000 : ℝ) (1301487687/2500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2335/16384 : ℝ)) (197979498257/200000000000 : ℝ) (123737186411/125000000000 : ℝ) (520595074791/1000000000000 : ℝ) (1301487687/2500000000 : ℝ) (206523614421/250000000000 : ℝ) (413047228851/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0554_exp_lower
  have heNumeric : (252388532401/125000000000 : ℝ)/4 ≤ Real.exp (-1367276806029/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252388532401/125000000000 : ℝ)/4 ≤ Real.exp ((1167/8192 : ℝ)-(413047228851/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1167/8192 : ℝ) (2335/16384 : ℝ) (413047228851/500000000000 : ℝ) (252388532401/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0555; no trusted numerical premise.
theorem cover7_leaf0555_exp_radius : (997457200459232833/1000000000000000000 : ℝ) ≤ Real.exp ((-73/3584 : ℝ)/8) ∧ Real.exp ((-73/3584 : ℝ)/8) ≤ (498728600229616417/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-73/3584 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0555_exp_lower : (459047424253152269/500000000000000000 : ℝ) ≤ Real.exp ((-2734546332349/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734546332349/4000000000000 : ℝ)/8) ≤ (918094848506304539/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734546332349/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0555_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019111933841/1000000000000 : ℝ) ≤ 4*Real.exp (2335/16384 : ℝ)*Real.exp (-mu (radius 7 (73/512 : ℝ))) ∧ (2019/1000 : ℝ) < (2019111933841/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (73/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0555_exp_radius
  have hrNumeric : (979837729107/1000000000000 : ℝ) ≤ Real.exp (-73/3584 : ℝ) ∧ Real.exp (-73/3584 : ℝ) ≤ (244959432277/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (979837729107/1000000000000 : ℝ) ≤ (radius 7 (73/512 : ℝ)) ∧ (radius 7 (73/512 : ℝ)) ≤ (244959432277/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (73/512 : ℝ)) (979837729107/1000000000000 : ℝ) (244959432277/250000000000 : ℝ) (99897478217/500000000000 : ℝ) (199794956439/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (73/512 : ℝ)) (979837729107/1000000000000 : ℝ) (244959432277/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (73/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (979837729107/1000000000000 : ℝ) (244959432277/250000000000 : ℝ) (989918864553/1000000000000 : ℝ) (494959432277/500000000000 : ℝ) (98986753109/100000000000 : ℝ) (989867531091/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (73/512 : ℝ)) 1 (989918864553/1000000000000 : ℝ) (494959432277/500000000000 : ℝ) (98986753109/100000000000 : ℝ) (989867531091/1000000000000 : ℝ) (989893197821/1000000000000 : ℝ) (989893197823/1000000000000 : ℝ) (61868324843/62500000000 : ℝ) (98989319749/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (73/512 : ℝ)) 2 (989893197821/1000000000000 : ℝ) (989893197823/1000000000000 : ℝ) (61868324843/62500000000 : ℝ) (98989319749/100000000000 : ℝ) (494946598827/500000000000 : ℝ) (989893197657/1000000000000 : ℝ) (494946598827/500000000000 : ℝ) (989893197657/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (73/512 : ℝ)) 3 (494946598827/500000000000 : ℝ) (989893197657/1000000000000 : ℝ) (494946598827/500000000000 : ℝ) (989893197657/1000000000000 : ℝ) (494946598827/500000000000 : ℝ) (989893197657/1000000000000 : ℝ) (494946598827/500000000000 : ℝ) (989893197657/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (73/512 : ℝ)) 4 (494946598827/500000000000 : ℝ) (989893197657/1000000000000 : ℝ) (494946598827/500000000000 : ℝ) (989893197657/1000000000000 : ℝ) (494946598827/500000000000 : ℝ) (989893197657/1000000000000 : ℝ) (494946598827/500000000000 : ℝ) (989893197657/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (73/512 : ℝ)) 5 (494946598827/500000000000 : ℝ) (989893197657/1000000000000 : ℝ) (494946598827/500000000000 : ℝ) (989893197657/1000000000000 : ℝ) (494946598827/500000000000 : ℝ) (989893197657/1000000000000 : ℝ) (494946598827/500000000000 : ℝ) (989893197657/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (73/512 : ℝ)) 6 (494946598827/500000000000 : ℝ) (989893197657/1000000000000 : ℝ) (494946598827/500000000000 : ℝ) (989893197657/1000000000000 : ℝ) (494946598827/500000000000 : ℝ) (989893197657/1000000000000 : ℝ) (494946598827/500000000000 : ℝ) (989893197657/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (73/512 : ℝ)) 7 (494946598827/500000000000 : ℝ) (989893197657/1000000000000 : ℝ) (494946598827/500000000000 : ℝ) (989893197657/1000000000000 : ℝ) (494946598827/500000000000 : ℝ) (989893197657/1000000000000 : ℝ) (494946598827/500000000000 : ℝ) (989893197657/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (73/512 : ℝ))) (99897478217/500000000000 : ℝ) (199794956439/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (73/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (99897478217/500000000000 : ℝ) (199794956439/1000000000000 : ℝ) (599897478217/1000000000000 : ℝ) (29994873911/50000000000 : ℝ) (446984291037/1000000000000 : ℝ) (446984291043/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (73/512 : ℝ))) 1 (599897478217/1000000000000 : ℝ) (29994873911/50000000000 : ℝ) (446984291037/1000000000000 : ℝ) (446984291043/1000000000000 : ℝ) (523440884627/1000000000000 : ℝ) (65430110579/125000000000 : ℝ) (517826948889/1000000000000 : ℝ) (258913474447/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (73/512 : ℝ))) 2 (523440884627/1000000000000 : ℝ) (65430110579/125000000000 : ℝ) (517826948889/1000000000000 : ℝ) (258913474447/500000000000 : ℝ) (260316958379/500000000000 : ℝ) (520633916763/1000000000000 : ℝ) (520626349899/1000000000000 : ℝ) (104125269981/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (73/512 : ℝ))) 3 (260316958379/500000000000 : ℝ) (520633916763/1000000000000 : ℝ) (520626349899/1000000000000 : ℝ) (104125269981/200000000000 : ℝ) (32539383333/62500000000 : ℝ) (260315066667/500000000000 : ℝ) (260315066657/500000000000 : ℝ) (520630133321/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (73/512 : ℝ))) 4 (32539383333/62500000000 : ℝ) (260315066667/500000000000 : ℝ) (260315066657/500000000000 : ℝ) (520630133321/1000000000000 : ℝ) (520630133321/1000000000000 : ℝ) (32539383333/62500000000 : ℝ) (13015753333/25000000000 : ℝ) (32539383333/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (73/512 : ℝ))) 5 (520630133321/1000000000000 : ℝ) (32539383333/62500000000 : ℝ) (13015753333/25000000000 : ℝ) (32539383333/62500000000 : ℝ) (13015753333/25000000000 : ℝ) (32539383333/62500000000 : ℝ) (13015753333/25000000000 : ℝ) (32539383333/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (73/512 : ℝ))) 6 (13015753333/25000000000 : ℝ) (32539383333/62500000000 : ℝ) (13015753333/25000000000 : ℝ) (32539383333/62500000000 : ℝ) (13015753333/25000000000 : ℝ) (32539383333/62500000000 : ℝ) (13015753333/25000000000 : ℝ) (32539383333/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (73/512 : ℝ))) 7 (13015753333/25000000000 : ℝ) (32539383333/62500000000 : ℝ) (13015753333/25000000000 : ℝ) (32539383333/62500000000 : ℝ) (13015753333/25000000000 : ℝ) (32539383333/62500000000 : ℝ) (13015753333/25000000000 : ℝ) (32539383333/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (73/512 : ℝ)) hmem 8 (494946598827/500000000000 : ℝ) (989893197657/1000000000000 : ℝ) (494946598827/500000000000 : ℝ) (989893197657/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (73/512 : ℝ))) hcmem 8 (13015753333/25000000000 : ℝ) (32539383333/62500000000 : ℝ) (13015753333/25000000000 : ℝ) (32539383333/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (73/512 : ℝ)) (494946598827/500000000000 : ℝ) (989893197657/1000000000000 : ℝ) (13015753333/25000000000 : ℝ) (32539383333/62500000000 : ℝ) (413076836457/500000000000 : ℝ) (826153672931/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0555_exp_lower
  have heNumeric : (2019111933841/1000000000000 : ℝ)/4 ≤ Real.exp (-2734546332349/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019111933841/1000000000000 : ℝ)/4 ≤ Real.exp ((2335/16384 : ℝ)-(826153672931/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2335/16384 : ℝ) (73/512 : ℝ) (826153672931/1000000000000 : ℝ) (2019111933841/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0556; no trusted numerical premise.
theorem cover7_leaf0556_exp_radius : (997456113317752373/1000000000000000000 : ℝ) ≤ Real.exp ((-2337/114688 : ℝ)/8) ∧ Real.exp ((-2337/114688 : ℝ)/8) ≤ (498728056658876187/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2337/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0556_exp_lower : (229523764824745923/250000000000000000 : ℝ) ≤ Real.exp ((-10681792911/15625000000 : ℝ)/8) ∧ Real.exp ((-10681792911/15625000000 : ℝ)/8) ≤ (918095059298983693/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10681792911/15625000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0556_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504778910629/250000000000 : ℝ) ≤ 4*Real.exp (73/512 : ℝ)*Real.exp (-mu (radius 7 (2337/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (504778910629/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2337/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0556_exp_radius
  have hrNumeric : (979829185637/1000000000000 : ℝ) ≤ Real.exp (-2337/114688 : ℝ) ∧ Real.exp (-2337/114688 : ℝ) ≤ (489914592819/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (979829185637/1000000000000 : ℝ) ≤ (radius 7 (2337/16384 : ℝ)) ∧ (radius 7 (2337/16384 : ℝ)) ≤ (489914592819/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2337/16384 : ℝ)) (979829185637/1000000000000 : ℝ) (489914592819/500000000000 : ℝ) (39967370177/200000000000 : ℝ) (199836850891/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2337/16384 : ℝ)) (979829185637/1000000000000 : ℝ) (489914592819/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2337/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (979829185637/1000000000000 : ℝ) (489914592819/500000000000 : ℝ) (494957296409/500000000000 : ℝ) (989914592819/1000000000000 : ℝ) (989863215619/1000000000000 : ℝ) (989863215621/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2337/16384 : ℝ)) 1 (494957296409/500000000000 : ℝ) (989914592819/1000000000000 : ℝ) (989863215619/1000000000000 : ℝ) (989863215621/1000000000000 : ℝ) (494944452109/500000000000 : ℝ) (49494445211/50000000000 : ℝ) (197977780777/200000000000 : ℝ) (989888903887/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2337/16384 : ℝ)) 2 (494944452109/500000000000 : ℝ) (49494445211/50000000000 : ℝ) (197977780777/200000000000 : ℝ) (989888903887/1000000000000 : ℝ) (989888904051/1000000000000 : ℝ) (494944452027/500000000000 : ℝ) (989888904051/1000000000000 : ℝ) (494944452027/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2337/16384 : ℝ)) 3 (989888904051/1000000000000 : ℝ) (494944452027/500000000000 : ℝ) (989888904051/1000000000000 : ℝ) (494944452027/500000000000 : ℝ) (989888904051/1000000000000 : ℝ) (494944452027/500000000000 : ℝ) (989888904051/1000000000000 : ℝ) (494944452027/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2337/16384 : ℝ)) 4 (989888904051/1000000000000 : ℝ) (494944452027/500000000000 : ℝ) (989888904051/1000000000000 : ℝ) (494944452027/500000000000 : ℝ) (989888904051/1000000000000 : ℝ) (494944452027/500000000000 : ℝ) (989888904051/1000000000000 : ℝ) (494944452027/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2337/16384 : ℝ)) 5 (989888904051/1000000000000 : ℝ) (494944452027/500000000000 : ℝ) (989888904051/1000000000000 : ℝ) (494944452027/500000000000 : ℝ) (989888904051/1000000000000 : ℝ) (494944452027/500000000000 : ℝ) (989888904051/1000000000000 : ℝ) (494944452027/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2337/16384 : ℝ)) 6 (989888904051/1000000000000 : ℝ) (494944452027/500000000000 : ℝ) (989888904051/1000000000000 : ℝ) (494944452027/500000000000 : ℝ) (989888904051/1000000000000 : ℝ) (494944452027/500000000000 : ℝ) (989888904051/1000000000000 : ℝ) (494944452027/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2337/16384 : ℝ)) 7 (989888904051/1000000000000 : ℝ) (494944452027/500000000000 : ℝ) (989888904051/1000000000000 : ℝ) (494944452027/500000000000 : ℝ) (989888904051/1000000000000 : ℝ) (494944452027/500000000000 : ℝ) (989888904051/1000000000000 : ℝ) (494944452027/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2337/16384 : ℝ))) (39967370177/200000000000 : ℝ) (199836850891/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2337/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (39967370177/200000000000 : ℝ) (199836850891/1000000000000 : ℝ) (299959212721/500000000000 : ℝ) (299959212723/500000000000 : ℝ) (447031152029/1000000000000 : ℝ) (447031152037/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2337/16384 : ℝ))) 1 (299959212721/500000000000 : ℝ) (299959212723/500000000000 : ℝ) (447031152029/1000000000000 : ℝ) (447031152037/1000000000000 : ℝ) (104694957747/200000000000 : ℝ) (261737394371/500000000000 : ℝ) (129465783329/250000000000 : ℝ) (129465783331/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2337/16384 : ℝ))) 2 (104694957747/200000000000 : ℝ) (261737394371/500000000000 : ℝ) (129465783329/250000000000 : ℝ) (129465783331/250000000000 : ℝ) (20826758441/40000000000 : ℝ) (520668961033/1000000000000 : ℝ) (260330700411/500000000000 : ℝ) (52066140083/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2337/16384 : ℝ))) 3 (20826758441/40000000000 : ℝ) (520668961033/1000000000000 : ℝ) (260330700411/500000000000 : ℝ) (52066140083/100000000000 : ℝ) (520665180923/1000000000000 : ℝ) (130166295233/250000000000 : ℝ) (520665180909/1000000000000 : ℝ) (260332590459/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2337/16384 : ℝ))) 4 (520665180923/1000000000000 : ℝ) (130166295233/250000000000 : ℝ) (520665180909/1000000000000 : ℝ) (260332590459/500000000000 : ℝ) (130166295229/250000000000 : ℝ) (20826607237/40000000000 : ℝ) (104133036183/200000000000 : ℝ) (20826607237/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2337/16384 : ℝ))) 5 (130166295229/250000000000 : ℝ) (20826607237/40000000000 : ℝ) (104133036183/200000000000 : ℝ) (20826607237/40000000000 : ℝ) (104133036183/200000000000 : ℝ) (20826607237/40000000000 : ℝ) (104133036183/200000000000 : ℝ) (20826607237/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2337/16384 : ℝ))) 6 (104133036183/200000000000 : ℝ) (20826607237/40000000000 : ℝ) (104133036183/200000000000 : ℝ) (20826607237/40000000000 : ℝ) (104133036183/200000000000 : ℝ) (20826607237/40000000000 : ℝ) (104133036183/200000000000 : ℝ) (20826607237/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2337/16384 : ℝ))) 7 (104133036183/200000000000 : ℝ) (20826607237/40000000000 : ℝ) (104133036183/200000000000 : ℝ) (20826607237/40000000000 : ℝ) (104133036183/200000000000 : ℝ) (20826607237/40000000000 : ℝ) (104133036183/200000000000 : ℝ) (20826607237/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2337/16384 : ℝ)) hmem 8 (989888904051/1000000000000 : ℝ) (494944452027/500000000000 : ℝ) (989888904051/1000000000000 : ℝ) (494944452027/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2337/16384 : ℝ))) hcmem 8 (104133036183/200000000000 : ℝ) (20826607237/40000000000 : ℝ) (104133036183/200000000000 : ℝ) (20826607237/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2337/16384 : ℝ)) (989888904051/1000000000000 : ℝ) (494944452027/500000000000 : ℝ) (104133036183/200000000000 : ℝ) (20826607237/40000000000 : ℝ) (206553217821/250000000000 : ℝ) (103276608913/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0556_exp_lower
  have heNumeric : (504778910629/250000000000 : ℝ)/4 ≤ Real.exp (-10681792911/15625000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504778910629/250000000000 : ℝ)/4 ≤ Real.exp ((73/512 : ℝ)-(103276608913/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (73/512 : ℝ) (2337/16384 : ℝ) (103276608913/125000000000 : ℝ) (504778910629/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0557; no trusted numerical premise.
theorem cover7_leaf0557_exp_radius : (498727513088728401/500000000000000000 : ℝ) ≤ Real.exp ((-167/8192 : ℝ)/8) ∧ Real.exp ((-167/8192 : ℝ)/8) ≤ (997455026177456803/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-167/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0557_exp_lower : (918095272025564171/1000000000000000000 : ℝ) ≤ Real.exp ((-2734531570679/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734531570679/4000000000000 : ℝ)/8) ≤ (229523818006391043/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734531570679/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0557_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019119385221/1000000000000 : ℝ) ≤ 4*Real.exp (2337/16384 : ℝ)*Real.exp (-mu (radius 7 (1169/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019119385221/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1169/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0557_exp_radius
  have hrNumeric : (489910321121/500000000000 : ℝ) ≤ Real.exp (-167/8192 : ℝ) ∧ Real.exp (-167/8192 : ℝ) ≤ (979820642243/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (489910321121/500000000000 : ℝ) ≤ (radius 7 (1169/8192 : ℝ)) ∧ (radius 7 (1169/8192 : ℝ)) ≤ (979820642243/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1169/8192 : ℝ)) (489910321121/500000000000 : ℝ) (979820642243/1000000000000 : ℝ) (199878735823/1000000000000 : ℝ) (199878735829/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1169/8192 : ℝ)) (489910321121/500000000000 : ℝ) (979820642243/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1169/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (489910321121/500000000000 : ℝ) (979820642243/1000000000000 : ℝ) (989910321121/1000000000000 : ℝ) (494955160561/500000000000 : ℝ) (123732362521/125000000000 : ℝ) (989858900169/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1169/8192 : ℝ)) 1 (989910321121/1000000000000 : ℝ) (494955160561/500000000000 : ℝ) (123732362521/125000000000 : ℝ) (989858900169/1000000000000 : ℝ) (247471152661/250000000000 : ℝ) (494942305323/500000000000 : ℝ) (98988461031/100000000000 : ℝ) (123735576289/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1169/8192 : ℝ)) 2 (247471152661/250000000000 : ℝ) (494942305323/500000000000 : ℝ) (98988461031/100000000000 : ℝ) (123735576289/125000000000 : ℝ) (989884610477/1000000000000 : ℝ) (989884610479/1000000000000 : ℝ) (247471152619/250000000000 : ℝ) (989884610479/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1169/8192 : ℝ)) 3 (989884610477/1000000000000 : ℝ) (989884610479/1000000000000 : ℝ) (247471152619/250000000000 : ℝ) (989884610479/1000000000000 : ℝ) (247471152619/250000000000 : ℝ) (989884610479/1000000000000 : ℝ) (247471152619/250000000000 : ℝ) (989884610479/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1169/8192 : ℝ)) 4 (247471152619/250000000000 : ℝ) (989884610479/1000000000000 : ℝ) (247471152619/250000000000 : ℝ) (989884610479/1000000000000 : ℝ) (247471152619/250000000000 : ℝ) (989884610479/1000000000000 : ℝ) (247471152619/250000000000 : ℝ) (989884610479/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1169/8192 : ℝ)) 5 (247471152619/250000000000 : ℝ) (989884610479/1000000000000 : ℝ) (247471152619/250000000000 : ℝ) (989884610479/1000000000000 : ℝ) (247471152619/250000000000 : ℝ) (989884610479/1000000000000 : ℝ) (247471152619/250000000000 : ℝ) (989884610479/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1169/8192 : ℝ)) 6 (247471152619/250000000000 : ℝ) (989884610479/1000000000000 : ℝ) (247471152619/250000000000 : ℝ) (989884610479/1000000000000 : ℝ) (247471152619/250000000000 : ℝ) (989884610479/1000000000000 : ℝ) (247471152619/250000000000 : ℝ) (989884610479/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1169/8192 : ℝ)) 7 (247471152619/250000000000 : ℝ) (989884610479/1000000000000 : ℝ) (247471152619/250000000000 : ℝ) (989884610479/1000000000000 : ℝ) (247471152619/250000000000 : ℝ) (989884610479/1000000000000 : ℝ) (247471152619/250000000000 : ℝ) (989884610479/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1169/8192 : ℝ))) (199878735823/1000000000000 : ℝ) (199878735829/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1169/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (199878735823/1000000000000 : ℝ) (199878735829/1000000000000 : ℝ) (599939367911/1000000000000 : ℝ) (119987873583/200000000000 : ℝ) (447077997471/1000000000000 : ℝ) (447077997479/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1169/8192 : ℝ))) 1 (599939367911/1000000000000 : ℝ) (119987873583/200000000000 : ℝ) (447077997471/1000000000000 : ℝ) (447077997479/1000000000000 : ℝ) (523508682691/1000000000000 : ℝ) (523508682697/1000000000000 : ℝ) (129474826513/250000000000 : ℝ) (517899306059/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1169/8192 : ℝ))) 2 (523508682691/1000000000000 : ℝ) (523508682697/1000000000000 : ℝ) (129474826513/250000000000 : ℝ) (517899306059/1000000000000 : ℝ) (520703994371/1000000000000 : ℝ) (260351997189/500000000000 : ℝ) (104139288163/200000000000 : ℝ) (260348220411/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1169/8192 : ℝ))) 3 (520703994371/1000000000000 : ℝ) (260351997189/500000000000 : ℝ) (104139288163/200000000000 : ℝ) (260348220411/500000000000 : ℝ) (520700217593/1000000000000 : ℝ) (81359409/156250000 : ℝ) (520700217579/1000000000000 : ℝ) (520700217587/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1169/8192 : ℝ))) 4 (520700217593/1000000000000 : ℝ) (81359409/156250000 : ℝ) (520700217579/1000000000000 : ℝ) (520700217587/1000000000000 : ℝ) (260350108793/500000000000 : ℝ) (260350108797/500000000000 : ℝ) (104140043517/200000000000 : ℝ) (260350108797/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1169/8192 : ℝ))) 5 (260350108793/500000000000 : ℝ) (260350108797/500000000000 : ℝ) (104140043517/200000000000 : ℝ) (260350108797/500000000000 : ℝ) (104140043517/200000000000 : ℝ) (260350108797/500000000000 : ℝ) (104140043517/200000000000 : ℝ) (260350108797/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1169/8192 : ℝ))) 6 (104140043517/200000000000 : ℝ) (260350108797/500000000000 : ℝ) (104140043517/200000000000 : ℝ) (260350108797/500000000000 : ℝ) (104140043517/200000000000 : ℝ) (260350108797/500000000000 : ℝ) (104140043517/200000000000 : ℝ) (260350108797/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1169/8192 : ℝ))) 7 (104140043517/200000000000 : ℝ) (260350108797/500000000000 : ℝ) (104140043517/200000000000 : ℝ) (260350108797/500000000000 : ℝ) (104140043517/200000000000 : ℝ) (260350108797/500000000000 : ℝ) (104140043517/200000000000 : ℝ) (260350108797/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1169/8192 : ℝ)) hmem 8 (247471152619/250000000000 : ℝ) (989884610479/1000000000000 : ℝ) (247471152619/250000000000 : ℝ) (989884610479/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1169/8192 : ℝ))) hcmem 8 (104140043517/200000000000 : ℝ) (260350108797/500000000000 : ℝ) (104140043517/200000000000 : ℝ) (260350108797/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1169/8192 : ℝ)) (247471152619/250000000000 : ℝ) (989884610479/1000000000000 : ℝ) (104140043517/200000000000 : ℝ) (260350108797/500000000000 : ℝ) (103284006601/125000000000 : ℝ) (413136026413/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0557_exp_lower
  have heNumeric : (2019119385221/1000000000000 : ℝ)/4 ≤ Real.exp (-2734531570679/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019119385221/1000000000000 : ℝ)/4 ≤ Real.exp ((2337/16384 : ℝ)-(413136026413/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2337/16384 : ℝ) (1169/8192 : ℝ) (413136026413/500000000000 : ℝ) (2019119385221/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0558; no trusted numerical premise.
theorem cover7_leaf0558_exp_radius : (249363212975105081/250000000000000000 : ℝ) ≤ Real.exp ((-585/28672 : ℝ)/8) ∧ Real.exp ((-585/28672 : ℝ)/8) ≤ (39898114076016813/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-585/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0558_exp_lower : (229522174696396701/250000000000000000 : ℝ) ≤ Real.exp ((-273476068027/400000000000 : ℝ)/8) ∧ Real.exp ((-273476068027/400000000000 : ℝ)/8) ≤ (183617739757117361/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-273476068027/400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0558_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019003738629/1000000000000 : ℝ) ≤ 4*Real.exp (1169/8192 : ℝ)*Real.exp (-mu (radius 7 (585/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (2019003738629/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (585/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0558_exp_radius
  have hrNumeric : (39192142227/40000000000 : ℝ) ≤ Real.exp (-585/28672 : ℝ) ∧ Real.exp (-585/28672 : ℝ) ≤ (244950888919/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39192142227/40000000000 : ℝ) ≤ (radius 7 (585/4096 : ℝ)) ∧ (radius 7 (585/4096 : ℝ)) ≤ (244950888919/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (585/4096 : ℝ)) (39192142227/40000000000 : ℝ) (244950888919/250000000000 : ℝ) (199962477191/1000000000000 : ℝ) (199962477197/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (585/4096 : ℝ)) (39192142227/40000000000 : ℝ) (244950888919/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (585/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39192142227/40000000000 : ℝ) (244950888919/250000000000 : ℝ) (989901777837/1000000000000 : ℝ) (494950888919/500000000000 : ℝ) (989850269321/1000000000000 : ℝ) (494925134661/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (585/4096 : ℝ)) 1 (989901777837/1000000000000 : ℝ) (494950888919/500000000000 : ℝ) (989850269321/1000000000000 : ℝ) (494925134661/500000000000 : ℝ) (989876023579/1000000000000 : ℝ) (49493801179/50000000000 : ℝ) (989876023243/1000000000000 : ℝ) (197975204649/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (585/4096 : ℝ)) 2 (989876023579/1000000000000 : ℝ) (49493801179/50000000000 : ℝ) (989876023243/1000000000000 : ℝ) (197975204649/200000000000 : ℝ) (989876023411/1000000000000 : ℝ) (989876023413/1000000000000 : ℝ) (98987602341/100000000000 : ℝ) (989876023413/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (585/4096 : ℝ)) 3 (989876023411/1000000000000 : ℝ) (989876023413/1000000000000 : ℝ) (98987602341/100000000000 : ℝ) (989876023413/1000000000000 : ℝ) (98987602341/100000000000 : ℝ) (989876023413/1000000000000 : ℝ) (98987602341/100000000000 : ℝ) (989876023413/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (585/4096 : ℝ)) 4 (98987602341/100000000000 : ℝ) (989876023413/1000000000000 : ℝ) (98987602341/100000000000 : ℝ) (989876023413/1000000000000 : ℝ) (98987602341/100000000000 : ℝ) (989876023413/1000000000000 : ℝ) (98987602341/100000000000 : ℝ) (989876023413/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (585/4096 : ℝ)) 5 (98987602341/100000000000 : ℝ) (989876023413/1000000000000 : ℝ) (98987602341/100000000000 : ℝ) (989876023413/1000000000000 : ℝ) (98987602341/100000000000 : ℝ) (989876023413/1000000000000 : ℝ) (98987602341/100000000000 : ℝ) (989876023413/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (585/4096 : ℝ)) 6 (98987602341/100000000000 : ℝ) (989876023413/1000000000000 : ℝ) (98987602341/100000000000 : ℝ) (989876023413/1000000000000 : ℝ) (98987602341/100000000000 : ℝ) (989876023413/1000000000000 : ℝ) (98987602341/100000000000 : ℝ) (989876023413/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (585/4096 : ℝ)) 7 (98987602341/100000000000 : ℝ) (989876023413/1000000000000 : ℝ) (98987602341/100000000000 : ℝ) (989876023413/1000000000000 : ℝ) (98987602341/100000000000 : ℝ) (989876023413/1000000000000 : ℝ) (98987602341/100000000000 : ℝ) (989876023413/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (585/4096 : ℝ))) (199962477191/1000000000000 : ℝ) (199962477197/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (585/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (199962477191/1000000000000 : ℝ) (199962477197/1000000000000 : ℝ) (119996247719/200000000000 : ℝ) (599981238599/1000000000000 : ℝ) (111792910439/250000000000 : ℝ) (447171641763/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (585/4096 : ℝ))) 1 (119996247719/200000000000 : ℝ) (599981238599/1000000000000 : ℝ) (111792910439/250000000000 : ℝ) (447171641763/1000000000000 : ℝ) (20943057607/40000000000 : ℝ) (523576440181/1000000000000 : ℝ) (258985808243/500000000000 : ℝ) (129492904123/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (585/4096 : ℝ))) 2 (20943057607/40000000000 : ℝ) (523576440181/1000000000000 : ℝ) (258985808243/500000000000 : ℝ) (129492904123/250000000000 : ℝ) (52077402833/100000000000 : ℝ) (520774028337/1000000000000 : ℝ) (104153297609/200000000000 : ℝ) (130191622013/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (585/4096 : ℝ))) 3 (52077402833/100000000000 : ℝ) (520774028337/1000000000000 : ℝ) (104153297609/200000000000 : ℝ) (130191622013/250000000000 : ℝ) (520770258187/1000000000000 : ℝ) (104154051639/200000000000 : ℝ) (520770258173/1000000000000 : ℝ) (520770258181/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (585/4096 : ℝ))) 4 (520770258187/1000000000000 : ℝ) (104154051639/200000000000 : ℝ) (520770258173/1000000000000 : ℝ) (520770258181/1000000000000 : ℝ) (26038512909/50000000000 : ℝ) (130192564547/250000000000 : ℝ) (520770258179/1000000000000 : ℝ) (130192564547/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (585/4096 : ℝ))) 5 (26038512909/50000000000 : ℝ) (130192564547/250000000000 : ℝ) (520770258179/1000000000000 : ℝ) (130192564547/250000000000 : ℝ) (520770258179/1000000000000 : ℝ) (130192564547/250000000000 : ℝ) (520770258179/1000000000000 : ℝ) (130192564547/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (585/4096 : ℝ))) 6 (520770258179/1000000000000 : ℝ) (130192564547/250000000000 : ℝ) (520770258179/1000000000000 : ℝ) (130192564547/250000000000 : ℝ) (520770258179/1000000000000 : ℝ) (130192564547/250000000000 : ℝ) (520770258179/1000000000000 : ℝ) (130192564547/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (585/4096 : ℝ))) 7 (520770258179/1000000000000 : ℝ) (130192564547/250000000000 : ℝ) (520770258179/1000000000000 : ℝ) (130192564547/250000000000 : ℝ) (520770258179/1000000000000 : ℝ) (130192564547/250000000000 : ℝ) (520770258179/1000000000000 : ℝ) (130192564547/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (585/4096 : ℝ)) hmem 8 (98987602341/100000000000 : ℝ) (989876023413/1000000000000 : ℝ) (98987602341/100000000000 : ℝ) (989876023413/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (585/4096 : ℝ))) hcmem 8 (520770258179/1000000000000 : ℝ) (130192564547/250000000000 : ℝ) (520770258179/1000000000000 : ℝ) (130192564547/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (585/4096 : ℝ)) (98987602341/100000000000 : ℝ) (989876023413/1000000000000 : ℝ) (520770258179/1000000000000 : ℝ) (130192564547/250000000000 : ℝ) (413195182681/500000000000 : ℝ) (41319518269/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0558_exp_lower
  have heNumeric : (2019003738629/1000000000000 : ℝ)/4 ≤ Real.exp (-273476068027/400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019003738629/1000000000000 : ℝ)/4 ≤ Real.exp ((1169/8192 : ℝ)-(41319518269/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1169/8192 : ℝ) (585/4096 : ℝ) (41319518269/50000000000 : ℝ) (2019003738629/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0559; no trusted numerical premise.
theorem cover7_leaf0559_exp_radius : (249362669407030847/250000000000000000 : ℝ) ≤ Real.exp ((-1171/57344 : ℝ)/8) ∧ Real.exp ((-1171/57344 : ℝ)/8) ≤ (997450677628123389/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1171/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0559_exp_lower : (459044568873224593/500000000000000000 : ℝ) ≤ Real.exp ((-683686345071/1000000000000 : ℝ)/8) ∧ Real.exp ((-683686345071/1000000000000 : ℝ)/8) ≤ (918089137746449187/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683686345071/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0559_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009505730663/500000000000 : ℝ) ≤ 4*Real.exp (585/4096 : ℝ)*Real.exp (-mu (radius 7 (1171/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (1009505730663/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1171/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0559_exp_radius
  have hrNumeric : (489893234703/500000000000 : ℝ) ≤ Real.exp (-1171/57344 : ℝ) ∧ Real.exp (-1171/57344 : ℝ) ≤ (979786469407/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (489893234703/500000000000 : ℝ) ≤ (radius 7 (1171/8192 : ℝ)) ∧ (radius 7 (1171/8192 : ℝ)) ≤ (979786469407/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1171/8192 : ℝ)) (489893234703/500000000000 : ℝ) (979786469407/1000000000000 : ℝ) (40009236117/200000000000 : ℝ) (200046180591/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1171/8192 : ℝ)) (489893234703/500000000000 : ℝ) (979786469407/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1171/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (489893234703/500000000000 : ℝ) (979786469407/1000000000000 : ℝ) (989893234703/1000000000000 : ℝ) (61868327169/62500000000 : ℝ) (989841638549/1000000000000 : ℝ) (19796832771/20000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1171/8192 : ℝ)) 1 (989893234703/1000000000000 : ℝ) (61868327169/62500000000 : ℝ) (989841638549/1000000000000 : ℝ) (19796832771/20000000000 : ℝ) (494933718313/500000000000 : ℝ) (989867436627/1000000000000 : ℝ) (989867436289/1000000000000 : ℝ) (989867436291/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1171/8192 : ℝ)) 2 (494933718313/500000000000 : ℝ) (989867436627/1000000000000 : ℝ) (989867436289/1000000000000 : ℝ) (989867436291/1000000000000 : ℝ) (989867436457/1000000000000 : ℝ) (989867436459/1000000000000 : ℝ) (989867436457/1000000000000 : ℝ) (989867436459/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1171/8192 : ℝ)) 3 (989867436457/1000000000000 : ℝ) (989867436459/1000000000000 : ℝ) (989867436457/1000000000000 : ℝ) (989867436459/1000000000000 : ℝ) (989867436457/1000000000000 : ℝ) (989867436459/1000000000000 : ℝ) (989867436457/1000000000000 : ℝ) (989867436459/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1171/8192 : ℝ)) 4 (989867436457/1000000000000 : ℝ) (989867436459/1000000000000 : ℝ) (989867436457/1000000000000 : ℝ) (989867436459/1000000000000 : ℝ) (989867436457/1000000000000 : ℝ) (989867436459/1000000000000 : ℝ) (989867436457/1000000000000 : ℝ) (989867436459/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1171/8192 : ℝ)) 5 (989867436457/1000000000000 : ℝ) (989867436459/1000000000000 : ℝ) (989867436457/1000000000000 : ℝ) (989867436459/1000000000000 : ℝ) (989867436457/1000000000000 : ℝ) (989867436459/1000000000000 : ℝ) (989867436457/1000000000000 : ℝ) (989867436459/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1171/8192 : ℝ)) 6 (989867436457/1000000000000 : ℝ) (989867436459/1000000000000 : ℝ) (989867436457/1000000000000 : ℝ) (989867436459/1000000000000 : ℝ) (989867436457/1000000000000 : ℝ) (989867436459/1000000000000 : ℝ) (989867436457/1000000000000 : ℝ) (989867436459/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1171/8192 : ℝ)) 7 (989867436457/1000000000000 : ℝ) (989867436459/1000000000000 : ℝ) (989867436457/1000000000000 : ℝ) (989867436459/1000000000000 : ℝ) (989867436457/1000000000000 : ℝ) (989867436459/1000000000000 : ℝ) (989867436457/1000000000000 : ℝ) (989867436459/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1171/8192 : ℝ))) (40009236117/200000000000 : ℝ) (200046180591/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1171/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (40009236117/200000000000 : ℝ) (200046180591/1000000000000 : ℝ) (150005772573/250000000000 : ℝ) (75002886287/125000000000 : ℝ) (447265223983/1000000000000 : ℝ) (447265223991/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1171/8192 : ℝ))) 1 (150005772573/250000000000 : ℝ) (75002886287/125000000000 : ℝ) (447265223983/1000000000000 : ℝ) (447265223991/1000000000000 : ℝ) (523644157137/1000000000000 : ℝ) (65455519643/125000000000 : ℝ) (518043880259/1000000000000 : ℝ) (259021940133/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1171/8192 : ℝ))) 2 (523644157137/1000000000000 : ℝ) (65455519643/125000000000 : ℝ) (518043880259/1000000000000 : ℝ) (259021940133/500000000000 : ℝ) (260422009349/500000000000 : ℝ) (104168803741/200000000000 : ℝ) (520836491653/1000000000000 : ℝ) (520836491661/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1171/8192 : ℝ))) 3 (260422009349/500000000000 : ℝ) (104168803741/200000000000 : ℝ) (520836491653/1000000000000 : ℝ) (520836491661/1000000000000 : ℝ) (20833610207/40000000000 : ℝ) (520840255183/1000000000000 : ℝ) (520840255161/1000000000000 : ℝ) (52084025517/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1171/8192 : ℝ))) 4 (20833610207/40000000000 : ℝ) (520840255183/1000000000000 : ℝ) (520840255161/1000000000000 : ℝ) (52084025517/100000000000 : ℝ) (8138128987/15625000000 : ℝ) (520840255177/1000000000000 : ℝ) (520840255167/1000000000000 : ℝ) (520840255177/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1171/8192 : ℝ))) 5 (8138128987/15625000000 : ℝ) (520840255177/1000000000000 : ℝ) (520840255167/1000000000000 : ℝ) (520840255177/1000000000000 : ℝ) (520840255167/1000000000000 : ℝ) (520840255177/1000000000000 : ℝ) (520840255167/1000000000000 : ℝ) (520840255177/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1171/8192 : ℝ))) 6 (520840255167/1000000000000 : ℝ) (520840255177/1000000000000 : ℝ) (520840255167/1000000000000 : ℝ) (520840255177/1000000000000 : ℝ) (520840255167/1000000000000 : ℝ) (520840255177/1000000000000 : ℝ) (520840255167/1000000000000 : ℝ) (520840255177/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1171/8192 : ℝ))) 7 (520840255167/1000000000000 : ℝ) (520840255177/1000000000000 : ℝ) (520840255167/1000000000000 : ℝ) (520840255177/1000000000000 : ℝ) (520840255167/1000000000000 : ℝ) (520840255177/1000000000000 : ℝ) (520840255167/1000000000000 : ℝ) (520840255177/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1171/8192 : ℝ)) hmem 8 (989867436457/1000000000000 : ℝ) (989867436459/1000000000000 : ℝ) (989867436457/1000000000000 : ℝ) (989867436459/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1171/8192 : ℝ))) hcmem 8 (520840255167/1000000000000 : ℝ) (520840255177/1000000000000 : ℝ) (520840255167/1000000000000 : ℝ) (520840255177/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1171/8192 : ℝ)) (989867436457/1000000000000 : ℝ) (989867436459/1000000000000 : ℝ) (520840255167/1000000000000 : ℝ) (520840255177/1000000000000 : ℝ) (413254305339/500000000000 : ℝ) (103313576337/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0559_exp_lower
  have heNumeric : (1009505730663/500000000000 : ℝ)/4 ≤ Real.exp (-683686345071/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009505730663/500000000000 : ℝ)/4 ≤ Real.exp ((585/4096 : ℝ)-(103313576337/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (585/4096 : ℝ) (1171/8192 : ℝ) (103313576337/125000000000 : ℝ) (1009505730663/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0560; no trusted numerical premise.
theorem cover7_leaf0560_exp_radius : (31170265730017687/31250000000000000 : ℝ) ≤ Real.exp ((-293/14336 : ℝ)/8) ∧ Real.exp ((-293/14336 : ℝ)/8) ≤ (199489700672113197/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-293/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0560_exp_lower : (918089584412243967/1000000000000000000 : ℝ) ≤ Real.exp ((-10938919247/16000000000 : ℝ)/8) ∧ Real.exp ((-10938919247/16000000000 : ℝ)/8) ≤ (448285929888791/488281250000000 : ℝ) := by
  have h := exp_small_bounds ((-10938919247/16000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0560_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019019319603/1000000000000 : ℝ) ≤ 4*Real.exp (1171/8192 : ℝ)*Real.exp (-mu (radius 7 (293/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (2019019319603/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (293/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0560_exp_radius
  have hrNumeric : (195953876687/200000000000 : ℝ) ≤ Real.exp (-293/14336 : ℝ) ∧ Real.exp (-293/14336 : ℝ) ≤ (244942345859/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (195953876687/200000000000 : ℝ) ≤ (radius 7 (293/2048 : ℝ)) ∧ (radius 7 (293/2048 : ℝ)) ≤ (244942345859/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (293/2048 : ℝ)) (195953876687/200000000000 : ℝ) (244942345859/250000000000 : ℝ) (200129846053/1000000000000 : ℝ) (200129846059/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (293/2048 : ℝ)) (195953876687/200000000000 : ℝ) (244942345859/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (293/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (195953876687/200000000000 : ℝ) (244942345859/250000000000 : ℝ) (989884691717/1000000000000 : ℝ) (494942345859/500000000000 : ℝ) (247458251963/250000000000 : ℝ) (494916503927/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (293/2048 : ℝ)) 1 (989884691717/1000000000000 : ℝ) (494942345859/500000000000 : ℝ) (247458251963/250000000000 : ℝ) (494916503927/500000000000 : ℝ) (123732356223/125000000000 : ℝ) (494929424893/500000000000 : ℝ) (989858849447/1000000000000 : ℝ) (989858849449/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (293/2048 : ℝ)) 2 (123732356223/125000000000 : ℝ) (494929424893/500000000000 : ℝ) (989858849447/1000000000000 : ℝ) (989858849449/1000000000000 : ℝ) (197971769923/200000000000 : ℝ) (494929424809/500000000000 : ℝ) (197971769923/200000000000 : ℝ) (494929424809/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (293/2048 : ℝ)) 3 (197971769923/200000000000 : ℝ) (494929424809/500000000000 : ℝ) (197971769923/200000000000 : ℝ) (494929424809/500000000000 : ℝ) (197971769923/200000000000 : ℝ) (494929424809/500000000000 : ℝ) (197971769923/200000000000 : ℝ) (494929424809/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (293/2048 : ℝ)) 4 (197971769923/200000000000 : ℝ) (494929424809/500000000000 : ℝ) (197971769923/200000000000 : ℝ) (494929424809/500000000000 : ℝ) (197971769923/200000000000 : ℝ) (494929424809/500000000000 : ℝ) (197971769923/200000000000 : ℝ) (494929424809/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (293/2048 : ℝ)) 5 (197971769923/200000000000 : ℝ) (494929424809/500000000000 : ℝ) (197971769923/200000000000 : ℝ) (494929424809/500000000000 : ℝ) (197971769923/200000000000 : ℝ) (494929424809/500000000000 : ℝ) (197971769923/200000000000 : ℝ) (494929424809/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (293/2048 : ℝ)) 6 (197971769923/200000000000 : ℝ) (494929424809/500000000000 : ℝ) (197971769923/200000000000 : ℝ) (494929424809/500000000000 : ℝ) (197971769923/200000000000 : ℝ) (494929424809/500000000000 : ℝ) (197971769923/200000000000 : ℝ) (494929424809/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (293/2048 : ℝ)) 7 (197971769923/200000000000 : ℝ) (494929424809/500000000000 : ℝ) (197971769923/200000000000 : ℝ) (494929424809/500000000000 : ℝ) (197971769923/200000000000 : ℝ) (494929424809/500000000000 : ℝ) (197971769923/200000000000 : ℝ) (494929424809/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (293/2048 : ℝ))) (200129846053/1000000000000 : ℝ) (200129846059/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (293/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (200129846053/1000000000000 : ℝ) (200129846059/1000000000000 : ℝ) (300032461513/500000000000 : ℝ) (60006492303/100000000000 : ℝ) (89471748849/200000000000 : ℝ) (447358744253/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (293/2048 : ℝ))) 1 (300032461513/500000000000 : ℝ) (60006492303/100000000000 : ℝ) (89471748849/200000000000 : ℝ) (447358744253/1000000000000 : ℝ) (104742366727/200000000000 : ℝ) (261855916821/500000000000 : ℝ) (518116097443/1000000000000 : ℝ) (518116097451/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (293/2048 : ℝ))) 2 (104742366727/200000000000 : ℝ) (261855916821/500000000000 : ℝ) (518116097443/1000000000000 : ℝ) (518116097451/1000000000000 : ℝ) (520913965539/1000000000000 : ℝ) (520913965547/1000000000000 : ℝ) (65113306463/125000000000 : ℝ) (520906451713/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (293/2048 : ℝ))) 3 (520913965539/1000000000000 : ℝ) (520913965547/1000000000000 : ℝ) (65113306463/125000000000 : ℝ) (520906451713/1000000000000 : ℝ) (520910208621/1000000000000 : ℝ) (52091020863/100000000000 : ℝ) (520910208607/1000000000000 : ℝ) (520910208617/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (293/2048 : ℝ))) 4 (520910208621/1000000000000 : ℝ) (52091020863/100000000000 : ℝ) (520910208607/1000000000000 : ℝ) (520910208617/1000000000000 : ℝ) (260455104307/500000000000 : ℝ) (32556888039/62500000000 : ℝ) (520910208613/1000000000000 : ℝ) (32556888039/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (293/2048 : ℝ))) 5 (260455104307/500000000000 : ℝ) (32556888039/62500000000 : ℝ) (520910208613/1000000000000 : ℝ) (32556888039/62500000000 : ℝ) (520910208613/1000000000000 : ℝ) (32556888039/62500000000 : ℝ) (520910208613/1000000000000 : ℝ) (32556888039/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (293/2048 : ℝ))) 6 (520910208613/1000000000000 : ℝ) (32556888039/62500000000 : ℝ) (520910208613/1000000000000 : ℝ) (32556888039/62500000000 : ℝ) (520910208613/1000000000000 : ℝ) (32556888039/62500000000 : ℝ) (520910208613/1000000000000 : ℝ) (32556888039/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (293/2048 : ℝ))) 7 (520910208613/1000000000000 : ℝ) (32556888039/62500000000 : ℝ) (520910208613/1000000000000 : ℝ) (32556888039/62500000000 : ℝ) (520910208613/1000000000000 : ℝ) (32556888039/62500000000 : ℝ) (520910208613/1000000000000 : ℝ) (32556888039/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (293/2048 : ℝ)) hmem 8 (197971769923/200000000000 : ℝ) (494929424809/500000000000 : ℝ) (197971769923/200000000000 : ℝ) (494929424809/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (293/2048 : ℝ))) hcmem 8 (520910208613/1000000000000 : ℝ) (32556888039/62500000000 : ℝ) (520910208613/1000000000000 : ℝ) (32556888039/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (293/2048 : ℝ)) (197971769923/200000000000 : ℝ) (494929424809/500000000000 : ℝ) (520910208613/1000000000000 : ℝ) (32556888039/62500000000 : ℝ) (413313394427/500000000000 : ℝ) (6613014311/8000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0560_exp_lower
  have heNumeric : (2019019319603/1000000000000 : ℝ)/4 ≤ Real.exp (-10938919247/16000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019019319603/1000000000000 : ℝ)/4 ≤ Real.exp ((1171/8192 : ℝ)-(6613014311/8000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1171/8192 : ℝ) (293/2048 : ℝ) (6613014311/8000000000 : ℝ) (2019019319603/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0561; no trusted numerical premise.
theorem cover7_leaf0561_exp_radius : (997446329097748103/1000000000000000000 : ℝ) ≤ Real.exp ((-1173/57344 : ℝ)/8) ∧ Real.exp ((-1173/57344 : ℝ)/8) ≤ (124680791137218513/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1173/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0561_exp_lower : (918090038771047223/1000000000000000000 : ℝ) ≤ Real.exp ((-683678493771/1000000000000 : ℝ)/8) ∧ Real.exp ((-683678493771/1000000000000 : ℝ)/8) ≤ (114761254846380903/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683678493771/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0561_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019027313253/1000000000000 : ℝ) ≤ 4*Real.exp (293/2048 : ℝ)*Real.exp (-mu (radius 7 (1173/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019027313253/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1173/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0561_exp_radius
  have hrNumeric : (979752297761/1000000000000 : ℝ) ≤ Real.exp (-1173/57344 : ℝ) ∧ Real.exp (-1173/57344 : ℝ) ≤ (489876148881/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (979752297761/1000000000000 : ℝ) ≤ (radius 7 (1173/8192 : ℝ)) ∧ (radius 7 (1173/8192 : ℝ)) ≤ (489876148881/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1173/8192 : ℝ)) (979752297761/1000000000000 : ℝ) (489876148881/500000000000 : ℝ) (200213473647/1000000000000 : ℝ) (200213473653/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1173/8192 : ℝ)) (979752297761/1000000000000 : ℝ) (489876148881/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1173/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (979752297761/1000000000000 : ℝ) (489876148881/500000000000 : ℝ) (12373451861/12500000000 : ℝ) (989876148881/1000000000000 : ℝ) (989824377231/1000000000000 : ℝ) (61864023577/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1173/8192 : ℝ)) 1 (12373451861/12500000000 : ℝ) (989876148881/1000000000000 : ℝ) (989824377231/1000000000000 : ℝ) (61864023577/62500000000 : ℝ) (197970052611/200000000000 : ℝ) (989850263057/1000000000000 : ℝ) (989850262717/1000000000000 : ℝ) (989850262719/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1173/8192 : ℝ)) 2 (197970052611/200000000000 : ℝ) (989850263057/1000000000000 : ℝ) (989850262717/1000000000000 : ℝ) (989850262719/1000000000000 : ℝ) (494925131443/500000000000 : ℝ) (123731282861/125000000000 : ℝ) (197970052577/200000000000 : ℝ) (123731282861/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1173/8192 : ℝ)) 3 (494925131443/500000000000 : ℝ) (123731282861/125000000000 : ℝ) (197970052577/200000000000 : ℝ) (123731282861/125000000000 : ℝ) (197970052577/200000000000 : ℝ) (123731282861/125000000000 : ℝ) (197970052577/200000000000 : ℝ) (123731282861/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1173/8192 : ℝ)) 4 (197970052577/200000000000 : ℝ) (123731282861/125000000000 : ℝ) (197970052577/200000000000 : ℝ) (123731282861/125000000000 : ℝ) (197970052577/200000000000 : ℝ) (123731282861/125000000000 : ℝ) (197970052577/200000000000 : ℝ) (123731282861/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1173/8192 : ℝ)) 5 (197970052577/200000000000 : ℝ) (123731282861/125000000000 : ℝ) (197970052577/200000000000 : ℝ) (123731282861/125000000000 : ℝ) (197970052577/200000000000 : ℝ) (123731282861/125000000000 : ℝ) (197970052577/200000000000 : ℝ) (123731282861/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1173/8192 : ℝ)) 6 (197970052577/200000000000 : ℝ) (123731282861/125000000000 : ℝ) (197970052577/200000000000 : ℝ) (123731282861/125000000000 : ℝ) (197970052577/200000000000 : ℝ) (123731282861/125000000000 : ℝ) (197970052577/200000000000 : ℝ) (123731282861/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1173/8192 : ℝ)) 7 (197970052577/200000000000 : ℝ) (123731282861/125000000000 : ℝ) (197970052577/200000000000 : ℝ) (123731282861/125000000000 : ℝ) (197970052577/200000000000 : ℝ) (123731282861/125000000000 : ℝ) (197970052577/200000000000 : ℝ) (123731282861/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1173/8192 : ℝ))) (200213473647/1000000000000 : ℝ) (200213473653/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1173/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (200213473647/1000000000000 : ℝ) (200213473653/1000000000000 : ℝ) (600106736823/1000000000000 : ℝ) (600106736827/1000000000000 : ℝ) (447452202639/1000000000000 : ℝ) (447452202647/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1173/8192 : ℝ))) 1 (600106736823/1000000000000 : ℝ) (600106736827/1000000000000 : ℝ) (447452202639/1000000000000 : ℝ) (447452202647/1000000000000 : ℝ) (523779469731/1000000000000 : ℝ) (523779469737/1000000000000 : ℝ) (518188268113/1000000000000 : ℝ) (12954706703/25000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1173/8192 : ℝ))) 2 (523779469731/1000000000000 : ℝ) (523779469737/1000000000000 : ℝ) (518188268113/1000000000000 : ℝ) (12954706703/25000000000 : ℝ) (260491934461/500000000000 : ℝ) (520983868929/1000000000000 : ℝ) (520976368267/1000000000000 : ℝ) (260488184137/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1173/8192 : ℝ))) 3 (260491934461/500000000000 : ℝ) (520983868929/1000000000000 : ℝ) (520976368267/1000000000000 : ℝ) (260488184137/500000000000 : ℝ) (260490059297/500000000000 : ℝ) (260490059301/500000000000 : ℝ) (520980118581/1000000000000 : ℝ) (520980118589/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1173/8192 : ℝ))) 4 (260490059297/500000000000 : ℝ) (260490059301/500000000000 : ℝ) (520980118581/1000000000000 : ℝ) (520980118589/1000000000000 : ℝ) (520980118587/1000000000000 : ℝ) (130245029649/250000000000 : ℝ) (520980118587/1000000000000 : ℝ) (130245029649/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1173/8192 : ℝ))) 5 (520980118587/1000000000000 : ℝ) (130245029649/250000000000 : ℝ) (520980118587/1000000000000 : ℝ) (130245029649/250000000000 : ℝ) (520980118587/1000000000000 : ℝ) (130245029649/250000000000 : ℝ) (520980118587/1000000000000 : ℝ) (130245029649/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1173/8192 : ℝ))) 6 (520980118587/1000000000000 : ℝ) (130245029649/250000000000 : ℝ) (520980118587/1000000000000 : ℝ) (130245029649/250000000000 : ℝ) (520980118587/1000000000000 : ℝ) (130245029649/250000000000 : ℝ) (520980118587/1000000000000 : ℝ) (130245029649/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1173/8192 : ℝ))) 7 (520980118587/1000000000000 : ℝ) (130245029649/250000000000 : ℝ) (520980118587/1000000000000 : ℝ) (130245029649/250000000000 : ℝ) (520980118587/1000000000000 : ℝ) (130245029649/250000000000 : ℝ) (520980118587/1000000000000 : ℝ) (130245029649/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1173/8192 : ℝ)) hmem 8 (197970052577/200000000000 : ℝ) (123731282861/125000000000 : ℝ) (197970052577/200000000000 : ℝ) (123731282861/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1173/8192 : ℝ))) hcmem 8 (520980118587/1000000000000 : ℝ) (130245029649/250000000000 : ℝ) (520980118587/1000000000000 : ℝ) (130245029649/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1173/8192 : ℝ)) (197970052577/200000000000 : ℝ) (123731282861/125000000000 : ℝ) (520980118587/1000000000000 : ℝ) (130245029649/250000000000 : ℝ) (826744900003/1000000000000 : ℝ) (826744900021/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0561_exp_lower
  have heNumeric : (2019027313253/1000000000000 : ℝ)/4 ≤ Real.exp (-683678493771/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019027313253/1000000000000 : ℝ)/4 ≤ Real.exp ((293/2048 : ℝ)-(826744900021/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (293/2048 : ℝ) (1173/8192 : ℝ) (826744900021/1000000000000 : ℝ) (2019027313253/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0562; no trusted numerical premise.
theorem cover7_leaf0562_exp_radius : (997444154839669733/1000000000000000000 : ℝ) ≤ Real.exp ((-587/28672 : ℝ)/8) ∧ Real.exp ((-587/28672 : ℝ)/8) ≤ (498722077419834867/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-587/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0562_exp_lower : (918090500813000901/1000000000000000000 : ℝ) ≤ Real.exp ((-273469787063/400000000000 : ℝ)/8) ∧ Real.exp ((-273469787063/400000000000 : ℝ)/8) ≤ (459045250406500451/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-273469787063/400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0562_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009517721051/500000000000 : ℝ) ≤ 4*Real.exp (1173/8192 : ℝ)*Real.exp (-mu (radius 7 (587/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (1009517721051/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (587/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0562_exp_radius
  have hrNumeric : (489867606193/500000000000 : ℝ) ≤ Real.exp (-587/28672 : ℝ) ∧ Real.exp (-587/28672 : ℝ) ≤ (979735212387/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (489867606193/500000000000 : ℝ) ≤ (radius 7 (587/4096 : ℝ)) ∧ (radius 7 (587/4096 : ℝ)) ≤ (979735212387/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (587/4096 : ℝ)) (489867606193/500000000000 : ℝ) (979735212387/1000000000000 : ℝ) (40059412681/200000000000 : ℝ) (200297063411/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (587/4096 : ℝ)) (489867606193/500000000000 : ℝ) (979735212387/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (587/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (489867606193/500000000000 : ℝ) (979735212387/1000000000000 : ℝ) (989867606193/1000000000000 : ℝ) (494933803097/500000000000 : ℝ) (197963149337/200000000000 : ℝ) (494907873343/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (587/4096 : ℝ)) 1 (989867606193/1000000000000 : ℝ) (494933803097/500000000000 : ℝ) (197963149337/200000000000 : ℝ) (494907873343/500000000000 : ℝ) (989841676439/1000000000000 : ℝ) (24746041911/25000000000 : ℝ) (989841676099/1000000000000 : ℝ) (989841676101/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (587/4096 : ℝ)) 2 (989841676439/1000000000000 : ℝ) (24746041911/25000000000 : ℝ) (989841676099/1000000000000 : ℝ) (989841676101/1000000000000 : ℝ) (989841676269/1000000000000 : ℝ) (989841676271/1000000000000 : ℝ) (247460419067/250000000000 : ℝ) (989841676271/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (587/4096 : ℝ)) 3 (989841676269/1000000000000 : ℝ) (989841676271/1000000000000 : ℝ) (247460419067/250000000000 : ℝ) (989841676271/1000000000000 : ℝ) (247460419067/250000000000 : ℝ) (989841676271/1000000000000 : ℝ) (247460419067/250000000000 : ℝ) (989841676271/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (587/4096 : ℝ)) 4 (247460419067/250000000000 : ℝ) (989841676271/1000000000000 : ℝ) (247460419067/250000000000 : ℝ) (989841676271/1000000000000 : ℝ) (247460419067/250000000000 : ℝ) (989841676271/1000000000000 : ℝ) (247460419067/250000000000 : ℝ) (989841676271/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (587/4096 : ℝ)) 5 (247460419067/250000000000 : ℝ) (989841676271/1000000000000 : ℝ) (247460419067/250000000000 : ℝ) (989841676271/1000000000000 : ℝ) (247460419067/250000000000 : ℝ) (989841676271/1000000000000 : ℝ) (247460419067/250000000000 : ℝ) (989841676271/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (587/4096 : ℝ)) 6 (247460419067/250000000000 : ℝ) (989841676271/1000000000000 : ℝ) (247460419067/250000000000 : ℝ) (989841676271/1000000000000 : ℝ) (247460419067/250000000000 : ℝ) (989841676271/1000000000000 : ℝ) (247460419067/250000000000 : ℝ) (989841676271/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (587/4096 : ℝ)) 7 (247460419067/250000000000 : ℝ) (989841676271/1000000000000 : ℝ) (247460419067/250000000000 : ℝ) (989841676271/1000000000000 : ℝ) (247460419067/250000000000 : ℝ) (989841676271/1000000000000 : ℝ) (247460419067/250000000000 : ℝ) (989841676271/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (587/4096 : ℝ))) (40059412681/200000000000 : ℝ) (200297063411/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (587/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (40059412681/200000000000 : ℝ) (200297063411/1000000000000 : ℝ) (300074265851/500000000000 : ℝ) (300074265853/500000000000 : ℝ) (223772799623/500000000000 : ℝ) (223772799627/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (587/4096 : ℝ))) 1 (300074265851/500000000000 : ℝ) (300074265853/500000000000 : ℝ) (223772799623/500000000000 : ℝ) (223772799627/500000000000 : ℝ) (261923532737/500000000000 : ℝ) (13096176637/25000000000 : ℝ) (518260392329/1000000000000 : ℝ) (32391274521/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (587/4096 : ℝ))) 2 (261923532737/500000000000 : ℝ) (13096176637/25000000000 : ℝ) (518260392329/1000000000000 : ℝ) (32391274521/62500000000 : ℝ) (521053728901/1000000000000 : ℝ) (130263432227/250000000000 : ℝ) (130261560349/250000000000 : ℝ) (521046241403/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (587/4096 : ℝ))) 3 (521053728901/1000000000000 : ℝ) (130263432227/250000000000 : ℝ) (130261560349/250000000000 : ℝ) (521046241403/1000000000000 : ℝ) (130262496287/250000000000 : ℝ) (130262496289/250000000000 : ℝ) (104209997027/200000000000 : ℝ) (521049985143/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (587/4096 : ℝ))) 4 (130262496287/250000000000 : ℝ) (130262496289/250000000000 : ℝ) (104209997027/200000000000 : ℝ) (521049985143/1000000000000 : ℝ) (521049985141/1000000000000 : ℝ) (10420999703/20000000000 : ℝ) (521049985141/1000000000000 : ℝ) (10420999703/20000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (587/4096 : ℝ))) 5 (521049985141/1000000000000 : ℝ) (10420999703/20000000000 : ℝ) (521049985141/1000000000000 : ℝ) (10420999703/20000000000 : ℝ) (521049985141/1000000000000 : ℝ) (10420999703/20000000000 : ℝ) (521049985141/1000000000000 : ℝ) (10420999703/20000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (587/4096 : ℝ))) 6 (521049985141/1000000000000 : ℝ) (10420999703/20000000000 : ℝ) (521049985141/1000000000000 : ℝ) (10420999703/20000000000 : ℝ) (521049985141/1000000000000 : ℝ) (10420999703/20000000000 : ℝ) (521049985141/1000000000000 : ℝ) (10420999703/20000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (587/4096 : ℝ))) 7 (521049985141/1000000000000 : ℝ) (10420999703/20000000000 : ℝ) (521049985141/1000000000000 : ℝ) (10420999703/20000000000 : ℝ) (521049985141/1000000000000 : ℝ) (10420999703/20000000000 : ℝ) (521049985141/1000000000000 : ℝ) (10420999703/20000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (587/4096 : ℝ)) hmem 8 (247460419067/250000000000 : ℝ) (989841676271/1000000000000 : ℝ) (247460419067/250000000000 : ℝ) (989841676271/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (587/4096 : ℝ))) hcmem 8 (521049985141/1000000000000 : ℝ) (10420999703/20000000000 : ℝ) (521049985141/1000000000000 : ℝ) (10420999703/20000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (587/4096 : ℝ)) (247460419067/250000000000 : ℝ) (989841676271/1000000000000 : ℝ) (521049985141/1000000000000 : ℝ) (10420999703/20000000000 : ℝ) (413431472101/500000000000 : ℝ) (41343147211/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0562_exp_lower
  have heNumeric : (1009517721051/500000000000 : ℝ)/4 ≤ Real.exp (-273469787063/400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009517721051/500000000000 : ℝ)/4 ≤ Real.exp ((1173/8192 : ℝ)-(41343147211/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1173/8192 : ℝ) (587/4096 : ℝ) (41343147211/50000000000 : ℝ) (1009517721051/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0563; no trusted numerical premise.
theorem cover7_leaf0563_exp_radius : (199488396117266173/200000000000000000 : ℝ) ≤ Real.exp ((-1175/57344 : ℝ)/8) ∧ Real.exp ((-1175/57344 : ℝ)/8) ≤ (498720990293165433/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1175/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0563_exp_lower : (229522742631373213/250000000000000000 : ℝ) ≤ Real.exp ((-683670374707/1000000000000 : ℝ)/8) ∧ Real.exp ((-683670374707/1000000000000 : ℝ)/8) ≤ (918090970525492853/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683670374707/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0563_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019043705931/1000000000000 : ℝ) ≤ 4*Real.exp (587/4096 : ℝ)*Real.exp (-mu (radius 7 (1175/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019043705931/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1175/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0563_exp_radius
  have hrNumeric : (979718127309/1000000000000 : ℝ) ≤ Real.exp (-1175/57344 : ℝ) ∧ Real.exp (-1175/57344 : ℝ) ≤ (97971812731/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (979718127309/1000000000000 : ℝ) ≤ (radius 7 (1175/8192 : ℝ)) ∧ (radius 7 (1175/8192 : ℝ)) ≤ (97971812731/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1175/8192 : ℝ)) (979718127309/1000000000000 : ℝ) (97971812731/100000000000 : ℝ) (10019030769/50000000000 : ℝ) (100190307693/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1175/8192 : ℝ)) (979718127309/1000000000000 : ℝ) (97971812731/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1175/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (979718127309/1000000000000 : ℝ) (97971812731/100000000000 : ℝ) (494929531827/500000000000 : ℝ) (197971812731/200000000000 : ℝ) (494903558107/500000000000 : ℝ) (123725889527/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1175/8192 : ℝ)) 1 (494929531827/500000000000 : ℝ) (197971812731/200000000000 : ℝ) (494903558107/500000000000 : ℝ) (123725889527/125000000000 : ℝ) (494916544967/500000000000 : ℝ) (61864568121/62500000000 : ℝ) (989833089593/1000000000000 : ℝ) (197966617919/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1175/8192 : ℝ)) 2 (494916544967/500000000000 : ℝ) (61864568121/62500000000 : ℝ) (989833089593/1000000000000 : ℝ) (197966617919/200000000000 : ℝ) (989833089763/1000000000000 : ℝ) (494916544883/500000000000 : ℝ) (989833089763/1000000000000 : ℝ) (494916544883/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1175/8192 : ℝ)) 3 (989833089763/1000000000000 : ℝ) (494916544883/500000000000 : ℝ) (989833089763/1000000000000 : ℝ) (494916544883/500000000000 : ℝ) (989833089763/1000000000000 : ℝ) (494916544883/500000000000 : ℝ) (989833089763/1000000000000 : ℝ) (494916544883/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1175/8192 : ℝ)) 4 (989833089763/1000000000000 : ℝ) (494916544883/500000000000 : ℝ) (989833089763/1000000000000 : ℝ) (494916544883/500000000000 : ℝ) (989833089763/1000000000000 : ℝ) (494916544883/500000000000 : ℝ) (989833089763/1000000000000 : ℝ) (494916544883/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1175/8192 : ℝ)) 5 (989833089763/1000000000000 : ℝ) (494916544883/500000000000 : ℝ) (989833089763/1000000000000 : ℝ) (494916544883/500000000000 : ℝ) (989833089763/1000000000000 : ℝ) (494916544883/500000000000 : ℝ) (989833089763/1000000000000 : ℝ) (494916544883/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1175/8192 : ℝ)) 6 (989833089763/1000000000000 : ℝ) (494916544883/500000000000 : ℝ) (989833089763/1000000000000 : ℝ) (494916544883/500000000000 : ℝ) (989833089763/1000000000000 : ℝ) (494916544883/500000000000 : ℝ) (989833089763/1000000000000 : ℝ) (494916544883/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1175/8192 : ℝ)) 7 (989833089763/1000000000000 : ℝ) (494916544883/500000000000 : ℝ) (989833089763/1000000000000 : ℝ) (494916544883/500000000000 : ℝ) (989833089763/1000000000000 : ℝ) (494916544883/500000000000 : ℝ) (989833089763/1000000000000 : ℝ) (494916544883/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1175/8192 : ℝ))) (10019030769/50000000000 : ℝ) (100190307693/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1175/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (10019030769/50000000000 : ℝ) (100190307693/500000000000 : ℝ) (60019030769/100000000000 : ℝ) (600190307693/1000000000000 : ℝ) (111909733541/250000000000 : ℝ) (111909733543/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1175/8192 : ℝ))) 1 (60019030769/100000000000 : ℝ) (600190307693/1000000000000 : ℝ) (111909733541/250000000000 : ℝ) (111909733543/250000000000 : ℝ) (523914620927/1000000000000 : ℝ) (523914620933/1000000000000 : ℝ) (518332470167/1000000000000 : ℝ) (259166235087/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1175/8192 : ℝ))) 2 (523914620927/1000000000000 : ℝ) (523914620933/1000000000000 : ℝ) (518332470167/1000000000000 : ℝ) (259166235087/500000000000 : ℝ) (521123545547/1000000000000 : ℝ) (260561772777/500000000000 : ℝ) (13027901779/25000000000 : ℝ) (521116071167/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1175/8192 : ℝ))) 3 (521123545547/1000000000000 : ℝ) (260561772777/500000000000 : ℝ) (13027901779/25000000000 : ℝ) (521116071167/1000000000000 : ℝ) (521119808353/1000000000000 : ℝ) (521119808361/1000000000000 : ℝ) (26055990417/50000000000 : ℝ) (130279952087/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1175/8192 : ℝ))) 4 (521119808353/1000000000000 : ℝ) (521119808361/1000000000000 : ℝ) (26055990417/50000000000 : ℝ) (130279952087/250000000000 : ℝ) (260559904173/500000000000 : ℝ) (104223961671/200000000000 : ℝ) (260559904173/500000000000 : ℝ) (104223961671/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1175/8192 : ℝ))) 5 (260559904173/500000000000 : ℝ) (104223961671/200000000000 : ℝ) (260559904173/500000000000 : ℝ) (104223961671/200000000000 : ℝ) (260559904173/500000000000 : ℝ) (104223961671/200000000000 : ℝ) (260559904173/500000000000 : ℝ) (104223961671/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1175/8192 : ℝ))) 6 (260559904173/500000000000 : ℝ) (104223961671/200000000000 : ℝ) (260559904173/500000000000 : ℝ) (104223961671/200000000000 : ℝ) (260559904173/500000000000 : ℝ) (104223961671/200000000000 : ℝ) (260559904173/500000000000 : ℝ) (104223961671/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1175/8192 : ℝ))) 7 (260559904173/500000000000 : ℝ) (104223961671/200000000000 : ℝ) (260559904173/500000000000 : ℝ) (104223961671/200000000000 : ℝ) (260559904173/500000000000 : ℝ) (104223961671/200000000000 : ℝ) (260559904173/500000000000 : ℝ) (104223961671/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1175/8192 : ℝ)) hmem 8 (989833089763/1000000000000 : ℝ) (494916544883/500000000000 : ℝ) (989833089763/1000000000000 : ℝ) (494916544883/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1175/8192 : ℝ))) hcmem 8 (260559904173/500000000000 : ℝ) (104223961671/200000000000 : ℝ) (260559904173/500000000000 : ℝ) (104223961671/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1175/8192 : ℝ)) (989833089763/1000000000000 : ℝ) (494916544883/500000000000 : ℝ) (260559904173/500000000000 : ℝ) (104223961671/200000000000 : ℝ) (206745230391/250000000000 : ℝ) (413490460791/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0563_exp_lower
  have heNumeric : (2019043705931/1000000000000 : ℝ)/4 ≤ Real.exp (-683670374707/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019043705931/1000000000000 : ℝ)/4 ≤ Real.exp ((587/4096 : ℝ)-(413490460791/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (587/4096 : ℝ) (1175/8192 : ℝ) (413490460791/500000000000 : ℝ) (2019043705931/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0564; no trusted numerical premise.
theorem cover7_leaf0564_exp_radius : (997439806337731487/1000000000000000000 : ℝ) ≤ Real.exp ((-21/1024 : ℝ)/8) ∧ Real.exp ((-21/1024 : ℝ)/8) ≤ (31169993948054109/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21/1024 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0564_exp_lower : (3672365791590071/4000000000000000 : ℝ) ≤ Real.exp ((-1367332430031/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367332430031/2000000000000 : ℝ)/8) ≤ (918091447897517751/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367332430031/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0564_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504763026137/250000000000 : ℝ) ≤ 4*Real.exp (1175/8192 : ℝ)*Real.exp (-mu (radius 7 (147/1024 : ℝ))) ∧ (2019/1000 : ℝ) < (504763026137/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (147/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0564_exp_radius
  have hrNumeric : (97970104253/100000000000 : ℝ) ≤ Real.exp (-21/1024 : ℝ) ∧ Real.exp (-21/1024 : ℝ) ≤ (979701042531/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (97970104253/100000000000 : ℝ) ≤ (radius 7 (147/1024 : ℝ)) ∧ (radius 7 (147/1024 : ℝ)) ≤ (979701042531/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (147/1024 : ℝ)) (97970104253/100000000000 : ℝ) (979701042531/1000000000000 : ℝ) (100232064809/500000000000 : ℝ) (25058016203/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (147/1024 : ℝ)) (97970104253/100000000000 : ℝ) (979701042531/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (147/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (97970104253/100000000000 : ℝ) (979701042531/1000000000000 : ℝ) (197970104253/200000000000 : ℝ) (494925260633/500000000000 : ℝ) (989798485819/1000000000000 : ℝ) (49489924291/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (147/1024 : ℝ)) 1 (197970104253/200000000000 : ℝ) (494925260633/500000000000 : ℝ) (989798485819/1000000000000 : ℝ) (49489924291/50000000000 : ℝ) (494912251771/500000000000 : ℝ) (989824503543/1000000000000 : ℝ) (1237280629/1250000000 : ℝ) (494912251601/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (147/1024 : ℝ)) 2 (494912251771/500000000000 : ℝ) (989824503543/1000000000000 : ℝ) (1237280629/1250000000 : ℝ) (494912251601/500000000000 : ℝ) (989824503371/1000000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (147/1024 : ℝ)) 3 (989824503371/1000000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (147/1024 : ℝ)) 4 (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (147/1024 : ℝ)) 5 (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (147/1024 : ℝ)) 6 (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (147/1024 : ℝ)) 7 (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (147/1024 : ℝ))) (100232064809/500000000000 : ℝ) (25058016203/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (147/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (100232064809/500000000000 : ℝ) (25058016203/125000000000 : ℝ) (600232064809/1000000000000 : ℝ) (150058016203/250000000000 : ℝ) (447732207483/1000000000000 : ℝ) (447732207491/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (147/1024 : ℝ))) 1 (600232064809/1000000000000 : ℝ) (150058016203/250000000000 : ℝ) (447732207483/1000000000000 : ℝ) (447732207491/1000000000000 : ℝ) (261991068073/500000000000 : ℝ) (65497767019/125000000000 : ℝ) (8100070339/15625000000 : ℝ) (518404501703/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (147/1024 : ℝ))) 2 (261991068073/500000000000 : ℝ) (65497767019/125000000000 : ℝ) (8100070339/15625000000 : ℝ) (518404501703/1000000000000 : ℝ) (521193318921/1000000000000 : ℝ) (32574582433/62500000000 : ℝ) (521185857623/1000000000000 : ℝ) (52118585763/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (147/1024 : ℝ))) 3 (521193318921/1000000000000 : ℝ) (32574582433/62500000000 : ℝ) (521185857623/1000000000000 : ℝ) (52118585763/100000000000 : ℝ) (32574349267/62500000000 : ℝ) (521189588279/1000000000000 : ℝ) (260594794129/500000000000 : ℝ) (260594794133/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (147/1024 : ℝ))) 4 (32574349267/62500000000 : ℝ) (521189588279/1000000000000 : ℝ) (260594794129/500000000000 : ℝ) (260594794133/500000000000 : ℝ) (104237917653/200000000000 : ℝ) (521189588273/1000000000000 : ℝ) (65148698533/125000000000 : ℝ) (521189588273/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (147/1024 : ℝ))) 5 (104237917653/200000000000 : ℝ) (521189588273/1000000000000 : ℝ) (65148698533/125000000000 : ℝ) (521189588273/1000000000000 : ℝ) (65148698533/125000000000 : ℝ) (521189588273/1000000000000 : ℝ) (65148698533/125000000000 : ℝ) (521189588273/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (147/1024 : ℝ))) 6 (65148698533/125000000000 : ℝ) (521189588273/1000000000000 : ℝ) (65148698533/125000000000 : ℝ) (521189588273/1000000000000 : ℝ) (65148698533/125000000000 : ℝ) (521189588273/1000000000000 : ℝ) (65148698533/125000000000 : ℝ) (521189588273/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (147/1024 : ℝ))) 7 (65148698533/125000000000 : ℝ) (521189588273/1000000000000 : ℝ) (65148698533/125000000000 : ℝ) (521189588273/1000000000000 : ℝ) (65148698533/125000000000 : ℝ) (521189588273/1000000000000 : ℝ) (65148698533/125000000000 : ℝ) (521189588273/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (147/1024 : ℝ)) hmem 8 (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (147/1024 : ℝ))) hcmem 8 (65148698533/125000000000 : ℝ) (521189588273/1000000000000 : ℝ) (65148698533/125000000000 : ℝ) (521189588273/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (147/1024 : ℝ)) (98982450337/100000000000 : ℝ) (989824503373/1000000000000 : ℝ) (65148698533/125000000000 : ℝ) (521189588273/1000000000000 : ℝ) (165419766437/200000000000 : ℝ) (827098832203/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0564_exp_lower
  have heNumeric : (504763026137/250000000000 : ℝ)/4 ≤ Real.exp (-1367332430031/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504763026137/250000000000 : ℝ)/4 ≤ Real.exp ((1175/8192 : ℝ)-(827098832203/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1175/8192 : ℝ) (147/1024 : ℝ) (827098832203/1000000000000 : ℝ) (504763026137/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0565; no trusted numerical premise.
theorem cover7_leaf0565_exp_radius : (99743763209387159/100000000000000000 : ℝ) ≤ Real.exp ((-1177/57344 : ℝ)/8) ∧ Real.exp ((-1177/57344 : ℝ)/8) ≤ (997437632093871591/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1177/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0565_exp_lower : (45904596645828927/50000000000000000 : ℝ) ≤ Real.exp ((-170915497173/250000000000 : ℝ)/8) ∧ Real.exp ((-170915497173/250000000000 : ℝ)/8) ≤ (918091932916578541/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-170915497173/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0565_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019060637733/1000000000000 : ℝ) ≤ 4*Real.exp (147/1024 : ℝ)*Real.exp (-mu (radius 7 (1177/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019060637733/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1177/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0565_exp_radius
  have hrNumeric : (30615123689/31250000000 : ℝ) ≤ Real.exp (-1177/57344 : ℝ) ∧ Real.exp (-1177/57344 : ℝ) ≤ (979683958049/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (30615123689/31250000000 : ℝ) ≤ (radius 7 (1177/8192 : ℝ)) ∧ (radius 7 (1177/8192 : ℝ)) ≤ (979683958049/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1177/8192 : ℝ)) (30615123689/31250000000 : ℝ) (979683958049/1000000000000 : ℝ) (50136901543/250000000000 : ℝ) (100273803089/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1177/8192 : ℝ)) (30615123689/31250000000 : ℝ) (979683958049/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1177/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (30615123689/31250000000 : ℝ) (979683958049/1000000000000 : ℝ) (61865123689/62500000000 : ℝ) (39593679161/40000000000 : ℝ) (494894927749/500000000000 : ℝ) (1979579711/2000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1177/8192 : ℝ)) 1 (61865123689/62500000000 : ℝ) (39593679161/40000000000 : ℝ) (494894927749/500000000000 : ℝ) (1979579711/2000000000 : ℝ) (989815917261/1000000000000 : ℝ) (989815917263/1000000000000 : ℝ) (989815916917/1000000000000 : ℝ) (24745397923/25000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1177/8192 : ℝ)) 2 (989815917261/1000000000000 : ℝ) (989815917263/1000000000000 : ℝ) (989815916917/1000000000000 : ℝ) (24745397923/25000000000 : ℝ) (989815917089/1000000000000 : ℝ) (247453979273/250000000000 : ℝ) (30931747409/31250000000 : ℝ) (247453979273/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1177/8192 : ℝ)) 3 (989815917089/1000000000000 : ℝ) (247453979273/250000000000 : ℝ) (30931747409/31250000000 : ℝ) (247453979273/250000000000 : ℝ) (30931747409/31250000000 : ℝ) (247453979273/250000000000 : ℝ) (30931747409/31250000000 : ℝ) (247453979273/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1177/8192 : ℝ)) 4 (30931747409/31250000000 : ℝ) (247453979273/250000000000 : ℝ) (30931747409/31250000000 : ℝ) (247453979273/250000000000 : ℝ) (30931747409/31250000000 : ℝ) (247453979273/250000000000 : ℝ) (30931747409/31250000000 : ℝ) (247453979273/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1177/8192 : ℝ)) 5 (30931747409/31250000000 : ℝ) (247453979273/250000000000 : ℝ) (30931747409/31250000000 : ℝ) (247453979273/250000000000 : ℝ) (30931747409/31250000000 : ℝ) (247453979273/250000000000 : ℝ) (30931747409/31250000000 : ℝ) (247453979273/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1177/8192 : ℝ)) 6 (30931747409/31250000000 : ℝ) (247453979273/250000000000 : ℝ) (30931747409/31250000000 : ℝ) (247453979273/250000000000 : ℝ) (30931747409/31250000000 : ℝ) (247453979273/250000000000 : ℝ) (30931747409/31250000000 : ℝ) (247453979273/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1177/8192 : ℝ)) 7 (30931747409/31250000000 : ℝ) (247453979273/250000000000 : ℝ) (30931747409/31250000000 : ℝ) (247453979273/250000000000 : ℝ) (30931747409/31250000000 : ℝ) (247453979273/250000000000 : ℝ) (30931747409/31250000000 : ℝ) (247453979273/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1177/8192 : ℝ))) (50136901543/250000000000 : ℝ) (100273803089/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1177/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (50136901543/250000000000 : ℝ) (100273803089/500000000000 : ℝ) (300136901543/500000000000 : ℝ) (600273803089/1000000000000 : ℝ) (4478254193/10000000000 : ℝ) (111956354827/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1177/8192 : ℝ))) 1 (300136901543/500000000000 : ℝ) (600273803089/1000000000000 : ℝ) (4478254193/10000000000 : ℝ) (111956354827/250000000000 : ℝ) (524049611193/1000000000000 : ℝ) (524049611199/1000000000000 : ℝ) (51847648699/100000000000 : ℝ) (518476486997/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1177/8192 : ℝ))) 2 (524049611193/1000000000000 : ℝ) (524049611199/1000000000000 : ℝ) (51847648699/100000000000 : ℝ) (518476486997/1000000000000 : ℝ) (521263049091/1000000000000 : ℝ) (260631524549/500000000000 : ℝ) (130313900213/250000000000 : ℝ) (521255600859/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1177/8192 : ℝ))) 3 (521263049091/1000000000000 : ℝ) (260631524549/500000000000 : ℝ) (130313900213/250000000000 : ℝ) (521255600859/1000000000000 : ℝ) (521259324971/1000000000000 : ℝ) (521259324979/1000000000000 : ℝ) (260629662479/500000000000 : ℝ) (260629662483/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1177/8192 : ℝ))) 4 (521259324971/1000000000000 : ℝ) (521259324979/1000000000000 : ℝ) (260629662479/500000000000 : ℝ) (260629662483/500000000000 : ℝ) (130314831241/250000000000 : ℝ) (521259324973/1000000000000 : ℝ) (130314831241/250000000000 : ℝ) (521259324973/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1177/8192 : ℝ))) 5 (130314831241/250000000000 : ℝ) (521259324973/1000000000000 : ℝ) (130314831241/250000000000 : ℝ) (521259324973/1000000000000 : ℝ) (130314831241/250000000000 : ℝ) (521259324973/1000000000000 : ℝ) (130314831241/250000000000 : ℝ) (521259324973/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1177/8192 : ℝ))) 6 (130314831241/250000000000 : ℝ) (521259324973/1000000000000 : ℝ) (130314831241/250000000000 : ℝ) (521259324973/1000000000000 : ℝ) (130314831241/250000000000 : ℝ) (521259324973/1000000000000 : ℝ) (130314831241/250000000000 : ℝ) (521259324973/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1177/8192 : ℝ))) 7 (130314831241/250000000000 : ℝ) (521259324973/1000000000000 : ℝ) (130314831241/250000000000 : ℝ) (521259324973/1000000000000 : ℝ) (130314831241/250000000000 : ℝ) (521259324973/1000000000000 : ℝ) (130314831241/250000000000 : ℝ) (521259324973/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1177/8192 : ℝ)) hmem 8 (30931747409/31250000000 : ℝ) (247453979273/250000000000 : ℝ) (30931747409/31250000000 : ℝ) (247453979273/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1177/8192 : ℝ))) hcmem 8 (130314831241/250000000000 : ℝ) (521259324973/1000000000000 : ℝ) (130314831241/250000000000 : ℝ) (521259324973/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1177/8192 : ℝ)) (30931747409/31250000000 : ℝ) (247453979273/250000000000 : ℝ) (130314831241/250000000000 : ℝ) (521259324973/1000000000000 : ℝ) (413608338087/500000000000 : ℝ) (25850521131/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0565_exp_lower
  have heNumeric : (2019060637733/1000000000000 : ℝ)/4 ≤ Real.exp (-170915497173/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019060637733/1000000000000 : ℝ)/4 ≤ Real.exp ((147/1024 : ℝ)-(25850521131/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (147/1024 : ℝ) (1177/8192 : ℝ) (25850521131/31250000000 : ℝ) (2019060637733/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0566; no trusted numerical premise.
theorem cover7_leaf0566_exp_radius : (249358864463687791/250000000000000000 : ℝ) ≤ Real.exp ((-589/28672 : ℝ)/8) ∧ Real.exp ((-589/28672 : ℝ)/8) ≤ (199487091570950233/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-589/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0566_exp_lower : (918092425573047371/1000000000000000000 : ℝ) ≤ Real.exp ((-1367315391641/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367315391641/2000000000000 : ℝ)/8) ≤ (229523106393261843/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367315391641/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0566_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (50476732633/25000000000 : ℝ) ≤ 4*Real.exp (1177/8192 : ℝ)*Real.exp (-mu (radius 7 (589/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (50476732633/25000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (589/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0566_exp_radius
  have hrNumeric : (195933374773/200000000000 : ℝ) ≤ Real.exp (-589/28672 : ℝ) ∧ Real.exp (-589/28672 : ℝ) ≤ (489833436933/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (195933374773/200000000000 : ℝ) ≤ (radius 7 (589/4096 : ℝ)) ∧ (radius 7 (589/4096 : ℝ)) ≤ (489833436933/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (589/4096 : ℝ)) (195933374773/200000000000 : ℝ) (489833436933/500000000000 : ℝ) (200631045079/1000000000000 : ℝ) (40126209017/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (589/4096 : ℝ)) (195933374773/200000000000 : ℝ) (489833436933/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (589/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (195933374773/200000000000 : ℝ) (489833436933/500000000000 : ℝ) (247458359233/250000000000 : ℝ) (989833436933/1000000000000 : ℝ) (989781225253/1000000000000 : ℝ) (197956245051/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (589/4096 : ℝ)) 1 (247458359233/250000000000 : ℝ) (989833436933/1000000000000 : ℝ) (989781225253/1000000000000 : ℝ) (197956245051/200000000000 : ℝ) (247451832773/250000000000 : ℝ) (494903665547/500000000000 : ℝ) (247451832687/250000000000 : ℝ) (3959229323/4000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (589/4096 : ℝ)) 2 (247451832773/250000000000 : ℝ) (494903665547/500000000000 : ℝ) (247451832687/250000000000 : ℝ) (3959229323/4000000000 : ℝ) (24745183273/25000000000 : ℝ) (494903665461/500000000000 : ℝ) (989807330919/1000000000000 : ℝ) (494903665461/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (589/4096 : ℝ)) 3 (24745183273/25000000000 : ℝ) (494903665461/500000000000 : ℝ) (989807330919/1000000000000 : ℝ) (494903665461/500000000000 : ℝ) (989807330919/1000000000000 : ℝ) (494903665461/500000000000 : ℝ) (989807330919/1000000000000 : ℝ) (494903665461/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (589/4096 : ℝ)) 4 (989807330919/1000000000000 : ℝ) (494903665461/500000000000 : ℝ) (989807330919/1000000000000 : ℝ) (494903665461/500000000000 : ℝ) (989807330919/1000000000000 : ℝ) (494903665461/500000000000 : ℝ) (989807330919/1000000000000 : ℝ) (494903665461/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (589/4096 : ℝ)) 5 (989807330919/1000000000000 : ℝ) (494903665461/500000000000 : ℝ) (989807330919/1000000000000 : ℝ) (494903665461/500000000000 : ℝ) (989807330919/1000000000000 : ℝ) (494903665461/500000000000 : ℝ) (989807330919/1000000000000 : ℝ) (494903665461/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (589/4096 : ℝ)) 6 (989807330919/1000000000000 : ℝ) (494903665461/500000000000 : ℝ) (989807330919/1000000000000 : ℝ) (494903665461/500000000000 : ℝ) (989807330919/1000000000000 : ℝ) (494903665461/500000000000 : ℝ) (989807330919/1000000000000 : ℝ) (494903665461/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (589/4096 : ℝ)) 7 (989807330919/1000000000000 : ℝ) (494903665461/500000000000 : ℝ) (989807330919/1000000000000 : ℝ) (494903665461/500000000000 : ℝ) (989807330919/1000000000000 : ℝ) (494903665461/500000000000 : ℝ) (989807330919/1000000000000 : ℝ) (494903665461/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (589/4096 : ℝ))) (200631045079/1000000000000 : ℝ) (40126209017/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (589/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (200631045079/1000000000000 : ℝ) (40126209017/200000000000 : ℝ) (600315522539/1000000000000 : ℝ) (600315522543/1000000000000 : ℝ) (13997455303/31250000000 : ℝ) (55989821213/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (589/4096 : ℝ))) 1 (600315522539/1000000000000 : ℝ) (600315522543/1000000000000 : ℝ) (13997455303/31250000000 : ℝ) (55989821213/125000000000 : ℝ) (524117046117/1000000000000 : ℝ) (131029261531/250000000000 : ℝ) (51854842611/100000000000 : ℝ) (259274213059/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (589/4096 : ℝ))) 2 (524117046117/1000000000000 : ℝ) (131029261531/250000000000 : ℝ) (51854842611/100000000000 : ℝ) (259274213059/500000000000 : ℝ) (521332736113/1000000000000 : ℝ) (521332736121/1000000000000 : ℝ) (260662650451/500000000000 : ℝ) (521325300911/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (589/4096 : ℝ))) 3 (521332736113/1000000000000 : ℝ) (521332736121/1000000000000 : ℝ) (260662650451/500000000000 : ℝ) (521325300911/1000000000000 : ℝ) (521329018507/1000000000000 : ℝ) (130332254629/250000000000 : ℝ) (260664509247/500000000000 : ℝ) (521329018503/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (589/4096 : ℝ))) 4 (521329018507/1000000000000 : ℝ) (130332254629/250000000000 : ℝ) (260664509247/500000000000 : ℝ) (521329018503/1000000000000 : ℝ) (1042658037/2000000000 : ℝ) (52132901851/100000000000 : ℝ) (1042658037/2000000000 : ℝ) (52132901851/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (589/4096 : ℝ))) 5 (1042658037/2000000000 : ℝ) (52132901851/100000000000 : ℝ) (1042658037/2000000000 : ℝ) (52132901851/100000000000 : ℝ) (1042658037/2000000000 : ℝ) (52132901851/100000000000 : ℝ) (1042658037/2000000000 : ℝ) (52132901851/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (589/4096 : ℝ))) 6 (1042658037/2000000000 : ℝ) (52132901851/100000000000 : ℝ) (1042658037/2000000000 : ℝ) (52132901851/100000000000 : ℝ) (1042658037/2000000000 : ℝ) (52132901851/100000000000 : ℝ) (1042658037/2000000000 : ℝ) (52132901851/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (589/4096 : ℝ))) 7 (1042658037/2000000000 : ℝ) (52132901851/100000000000 : ℝ) (1042658037/2000000000 : ℝ) (52132901851/100000000000 : ℝ) (1042658037/2000000000 : ℝ) (52132901851/100000000000 : ℝ) (1042658037/2000000000 : ℝ) (52132901851/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (589/4096 : ℝ)) hmem 8 (989807330919/1000000000000 : ℝ) (494903665461/500000000000 : ℝ) (989807330919/1000000000000 : ℝ) (494903665461/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (589/4096 : ℝ))) hcmem 8 (1042658037/2000000000 : ℝ) (52132901851/100000000000 : ℝ) (1042658037/2000000000 : ℝ) (52132901851/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (589/4096 : ℝ)) (989807330919/1000000000000 : ℝ) (494903665461/500000000000 : ℝ) (1042658037/2000000000 : ℝ) (52132901851/100000000000 : ℝ) (827334453613/1000000000000 : ℝ) (827334453633/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0566_exp_lower
  have heNumeric : (50476732633/25000000000 : ℝ)/4 ≤ Real.exp (-1367315391641/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (50476732633/25000000000 : ℝ)/4 ≤ Real.exp ((1177/8192 : ℝ)-(827334453633/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1177/8192 : ℝ) (589/4096 : ℝ) (827334453633/1000000000000 : ℝ) (50476732633/25000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0567; no trusted numerical premise.
theorem cover7_leaf0567_exp_radius : (997433283620370197/1000000000000000000 : ℝ) ≤ Real.exp ((-1179/57344 : ℝ)/8) ∧ Real.exp ((-1179/57344 : ℝ)/8) ≤ (498716641810185099/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1179/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0567_exp_lower : (459046462927099/500000000000000 : ℝ) ≤ Real.exp ((-10682083383/15625000000 : ℝ)/8) ∧ Real.exp ((-10682083383/15625000000 : ℝ)/8) ≤ (918092925854198001/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10682083383/15625000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0567_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403815621417/200000000000 : ℝ) ≤ 4*Real.exp (589/4096 : ℝ)*Real.exp (-mu (radius 7 (1179/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (403815621417/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1179/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0567_exp_radius
  have hrNumeric : (979649789979/1000000000000 : ℝ) ≤ Real.exp (-1179/57344 : ℝ) ∧ Real.exp (-1179/57344 : ℝ) ≤ (48982489499/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (979649789979/1000000000000 : ℝ) ≤ (radius 7 (1179/8192 : ℝ)) ∧ (radius 7 (1179/8192 : ℝ)) ≤ (48982489499/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1179/8192 : ℝ)) (979649789979/1000000000000 : ℝ) (48982489499/50000000000 : ℝ) (50178611599/250000000000 : ℝ) (100357223201/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1179/8192 : ℝ)) (979649789979/1000000000000 : ℝ) (48982489499/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1179/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (979649789979/1000000000000 : ℝ) (48982489499/50000000000 : ℝ) (989824894989/1000000000000 : ℝ) (98982489499/100000000000 : ℝ) (989772595083/1000000000000 : ℝ) (197954519017/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1179/8192 : ℝ)) 1 (989824894989/1000000000000 : ℝ) (98982489499/100000000000 : ℝ) (989772595083/1000000000000 : ℝ) (197954519017/200000000000 : ℝ) (247449686259/250000000000 : ℝ) (494899372519/500000000000 : ℝ) (98979874469/100000000000 : ℝ) (989798744693/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1179/8192 : ℝ)) 2 (247449686259/250000000000 : ℝ) (494899372519/500000000000 : ℝ) (98979874469/100000000000 : ℝ) (989798744693/1000000000000 : ℝ) (989798744863/1000000000000 : ℝ) (494899372433/500000000000 : ℝ) (494899372431/500000000000 : ℝ) (494899372433/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1179/8192 : ℝ)) 3 (989798744863/1000000000000 : ℝ) (494899372433/500000000000 : ℝ) (494899372431/500000000000 : ℝ) (494899372433/500000000000 : ℝ) (494899372431/500000000000 : ℝ) (494899372433/500000000000 : ℝ) (494899372431/500000000000 : ℝ) (494899372433/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1179/8192 : ℝ)) 4 (494899372431/500000000000 : ℝ) (494899372433/500000000000 : ℝ) (494899372431/500000000000 : ℝ) (494899372433/500000000000 : ℝ) (494899372431/500000000000 : ℝ) (494899372433/500000000000 : ℝ) (494899372431/500000000000 : ℝ) (494899372433/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1179/8192 : ℝ)) 5 (494899372431/500000000000 : ℝ) (494899372433/500000000000 : ℝ) (494899372431/500000000000 : ℝ) (494899372433/500000000000 : ℝ) (494899372431/500000000000 : ℝ) (494899372433/500000000000 : ℝ) (494899372431/500000000000 : ℝ) (494899372433/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1179/8192 : ℝ)) 6 (494899372431/500000000000 : ℝ) (494899372433/500000000000 : ℝ) (494899372431/500000000000 : ℝ) (494899372433/500000000000 : ℝ) (494899372431/500000000000 : ℝ) (494899372433/500000000000 : ℝ) (494899372431/500000000000 : ℝ) (494899372433/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1179/8192 : ℝ)) 7 (494899372431/500000000000 : ℝ) (494899372433/500000000000 : ℝ) (494899372431/500000000000 : ℝ) (494899372433/500000000000 : ℝ) (494899372431/500000000000 : ℝ) (494899372433/500000000000 : ℝ) (494899372431/500000000000 : ℝ) (494899372433/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1179/8192 : ℝ))) (50178611599/250000000000 : ℝ) (100357223201/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1179/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (50178611599/250000000000 : ℝ) (100357223201/500000000000 : ℝ) (300178611599/500000000000 : ℝ) (600357223201/1000000000000 : ℝ) (112002914693/250000000000 : ℝ) (22400582939/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1179/8192 : ℝ))) 1 (300178611599/500000000000 : ℝ) (600357223201/1000000000000 : ℝ) (112002914693/250000000000 : ℝ) (22400582939/50000000000 : ℝ) (104836888197/200000000000 : ℝ) (524184440991/1000000000000 : ℝ) (103724063827/200000000000 : ℝ) (259310159571/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1179/8192 : ℝ))) 2 (104836888197/200000000000 : ℝ) (524184440991/1000000000000 : ℝ) (103724063827/200000000000 : ℝ) (259310159571/500000000000 : ℝ) (26070119003/50000000000 : ℝ) (521402380067/1000000000000 : ℝ) (521394957847/1000000000000 : ℝ) (104278991571/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1179/8192 : ℝ))) 3 (26070119003/50000000000 : ℝ) (521402380067/1000000000000 : ℝ) (521394957847/1000000000000 : ℝ) (104278991571/200000000000 : ℝ) (521398668953/1000000000000 : ℝ) (521398668961/1000000000000 : ℝ) (26069933447/50000000000 : ℝ) (130349667237/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1179/8192 : ℝ))) 4 (521398668953/1000000000000 : ℝ) (521398668961/1000000000000 : ℝ) (26069933447/50000000000 : ℝ) (130349667237/250000000000 : ℝ) (260699334473/500000000000 : ℝ) (104279733791/200000000000 : ℝ) (260699334473/500000000000 : ℝ) (104279733791/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1179/8192 : ℝ))) 5 (260699334473/500000000000 : ℝ) (104279733791/200000000000 : ℝ) (260699334473/500000000000 : ℝ) (104279733791/200000000000 : ℝ) (260699334473/500000000000 : ℝ) (104279733791/200000000000 : ℝ) (260699334473/500000000000 : ℝ) (104279733791/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1179/8192 : ℝ))) 6 (260699334473/500000000000 : ℝ) (104279733791/200000000000 : ℝ) (260699334473/500000000000 : ℝ) (104279733791/200000000000 : ℝ) (260699334473/500000000000 : ℝ) (104279733791/200000000000 : ℝ) (260699334473/500000000000 : ℝ) (104279733791/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1179/8192 : ℝ))) 7 (260699334473/500000000000 : ℝ) (104279733791/200000000000 : ℝ) (260699334473/500000000000 : ℝ) (104279733791/200000000000 : ℝ) (260699334473/500000000000 : ℝ) (104279733791/200000000000 : ℝ) (260699334473/500000000000 : ℝ) (104279733791/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1179/8192 : ℝ)) hmem 8 (494899372431/500000000000 : ℝ) (494899372433/500000000000 : ℝ) (494899372431/500000000000 : ℝ) (494899372433/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1179/8192 : ℝ))) hcmem 8 (260699334473/500000000000 : ℝ) (104279733791/200000000000 : ℝ) (260699334473/500000000000 : ℝ) (104279733791/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1179/8192 : ℝ)) (494899372431/500000000000 : ℝ) (494899372433/500000000000 : ℝ) (260699334473/500000000000 : ℝ) (104279733791/200000000000 : ℝ) (413726082309/500000000000 : ℝ) (827452164637/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0567_exp_lower
  have heNumeric : (403815621417/200000000000 : ℝ)/4 ≤ Real.exp (-10682083383/15625000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403815621417/200000000000 : ℝ)/4 ≤ Real.exp ((589/4096 : ℝ)-(827452164637/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (589/4096 : ℝ) (1179/8192 : ℝ) (827452164637/1000000000000 : ℝ) (403815621417/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0568; no trusted numerical premise.
theorem cover7_leaf0568_exp_radius : (24935777734768217/25000000000000000 : ℝ) ≤ Real.exp ((-295/14336 : ℝ)/8) ∧ Real.exp ((-295/14336 : ℝ)/8) ≤ (997431109390728681/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-295/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0568_exp_lower : (114761679218771673/125000000000000000 : ℝ) ≤ Real.exp ((-273459564341/400000000000 : ℝ)/8) ∧ Real.exp ((-273459564341/400000000000 : ℝ)/8) ≤ (183618686750034677/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-273459564341/400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0568_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019087042857/1000000000000 : ℝ) ≤ 4*Real.exp (1179/8192 : ℝ)*Real.exp (-mu (radius 7 (295/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (2019087042857/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (295/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0568_exp_radius
  have hrNumeric : (122454088299/125000000000 : ℝ) ≤ Real.exp (-295/14336 : ℝ) ∧ Real.exp (-295/14336 : ℝ) ≤ (979632706393/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122454088299/125000000000 : ℝ) ≤ (radius 7 (295/2048 : ℝ)) ∧ (radius 7 (295/2048 : ℝ)) ≤ (979632706393/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (295/2048 : ℝ)) (122454088299/125000000000 : ℝ) (979632706393/1000000000000 : ℝ) (2509972627/12500000000 : ℝ) (100398905083/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (295/2048 : ℝ)) (122454088299/125000000000 : ℝ) (979632706393/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (295/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122454088299/125000000000 : ℝ) (979632706393/1000000000000 : ℝ) (247454088299/250000000000 : ℝ) (989816353197/1000000000000 : ℝ) (989763964989/1000000000000 : ℝ) (989763964991/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (295/2048 : ℝ)) 1 (247454088299/250000000000 : ℝ) (989816353197/1000000000000 : ℝ) (989763964989/1000000000000 : ℝ) (989763964991/1000000000000 : ℝ) (247447539773/250000000000 : ℝ) (494895079547/500000000000 : ℝ) (197958031749/200000000000 : ℝ) (247447539687/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (295/2048 : ℝ)) 2 (247447539773/250000000000 : ℝ) (494895079547/500000000000 : ℝ) (197958031749/200000000000 : ℝ) (247447539687/250000000000 : ℝ) (494895079459/500000000000 : ℝ) (989790158921/1000000000000 : ℝ) (494895079459/500000000000 : ℝ) (989790158921/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (295/2048 : ℝ)) 3 (494895079459/500000000000 : ℝ) (989790158921/1000000000000 : ℝ) (494895079459/500000000000 : ℝ) (989790158921/1000000000000 : ℝ) (494895079459/500000000000 : ℝ) (989790158921/1000000000000 : ℝ) (494895079459/500000000000 : ℝ) (989790158921/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (295/2048 : ℝ)) 4 (494895079459/500000000000 : ℝ) (989790158921/1000000000000 : ℝ) (494895079459/500000000000 : ℝ) (989790158921/1000000000000 : ℝ) (494895079459/500000000000 : ℝ) (989790158921/1000000000000 : ℝ) (494895079459/500000000000 : ℝ) (989790158921/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (295/2048 : ℝ)) 5 (494895079459/500000000000 : ℝ) (989790158921/1000000000000 : ℝ) (494895079459/500000000000 : ℝ) (989790158921/1000000000000 : ℝ) (494895079459/500000000000 : ℝ) (989790158921/1000000000000 : ℝ) (494895079459/500000000000 : ℝ) (989790158921/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (295/2048 : ℝ)) 6 (494895079459/500000000000 : ℝ) (989790158921/1000000000000 : ℝ) (494895079459/500000000000 : ℝ) (989790158921/1000000000000 : ℝ) (494895079459/500000000000 : ℝ) (989790158921/1000000000000 : ℝ) (494895079459/500000000000 : ℝ) (989790158921/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (295/2048 : ℝ)) 7 (494895079459/500000000000 : ℝ) (989790158921/1000000000000 : ℝ) (494895079459/500000000000 : ℝ) (989790158921/1000000000000 : ℝ) (494895079459/500000000000 : ℝ) (989790158921/1000000000000 : ℝ) (494895079459/500000000000 : ℝ) (989790158921/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (295/2048 : ℝ))) (2509972627/12500000000 : ℝ) (100398905083/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (295/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (2509972627/12500000000 : ℝ) (100398905083/500000000000 : ℝ) (15009972627/25000000000 : ℝ) (600398905083/1000000000000 : ℝ) (448104686607/1000000000000 : ℝ) (89620937323/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (295/2048 : ℝ))) 1 (15009972627/25000000000 : ℝ) (600398905083/1000000000000 : ℝ) (448104686607/1000000000000 : ℝ) (89620937323/200000000000 : ℝ) (524251795843/1000000000000 : ℝ) (524251795849/1000000000000 : ℝ) (4149537329/8000000000 : ℝ) (129673041533/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (295/2048 : ℝ))) 2 (524251795843/1000000000000 : ℝ) (524251795849/1000000000000 : ℝ) (4149537329/8000000000 : ℝ) (129673041533/250000000000 : ℝ) (65183997623/125000000000 : ℝ) (521471980991/1000000000000 : ℝ) (26073228587/50000000000 : ℝ) (130366142937/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (295/2048 : ℝ))) 3 (65183997623/125000000000 : ℝ) (521471980991/1000000000000 : ℝ) (26073228587/50000000000 : ℝ) (130366142937/250000000000 : ℝ) (260734138181/500000000000 : ℝ) (52146827637/100000000000 : ℝ) (130367069087/250000000000 : ℝ) (521468276357/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (295/2048 : ℝ))) 4 (260734138181/500000000000 : ℝ) (52146827637/100000000000 : ℝ) (130367069087/250000000000 : ℝ) (521468276357/1000000000000 : ℝ) (104293655271/200000000000 : ℝ) (130367069091/250000000000 : ℝ) (260734138177/500000000000 : ℝ) (130367069091/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (295/2048 : ℝ))) 5 (104293655271/200000000000 : ℝ) (130367069091/250000000000 : ℝ) (260734138177/500000000000 : ℝ) (130367069091/250000000000 : ℝ) (260734138177/500000000000 : ℝ) (130367069091/250000000000 : ℝ) (260734138177/500000000000 : ℝ) (130367069091/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (295/2048 : ℝ))) 6 (260734138177/500000000000 : ℝ) (130367069091/250000000000 : ℝ) (260734138177/500000000000 : ℝ) (130367069091/250000000000 : ℝ) (260734138177/500000000000 : ℝ) (130367069091/250000000000 : ℝ) (260734138177/500000000000 : ℝ) (130367069091/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (295/2048 : ℝ))) 7 (260734138177/500000000000 : ℝ) (130367069091/250000000000 : ℝ) (260734138177/500000000000 : ℝ) (130367069091/250000000000 : ℝ) (260734138177/500000000000 : ℝ) (130367069091/250000000000 : ℝ) (260734138177/500000000000 : ℝ) (130367069091/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (295/2048 : ℝ)) hmem 8 (494895079459/500000000000 : ℝ) (989790158921/1000000000000 : ℝ) (494895079459/500000000000 : ℝ) (989790158921/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (295/2048 : ℝ))) hcmem 8 (260734138177/500000000000 : ℝ) (130367069091/250000000000 : ℝ) (260734138177/500000000000 : ℝ) (130367069091/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (295/2048 : ℝ)) (494895079459/500000000000 : ℝ) (989790158921/1000000000000 : ℝ) (260734138177/500000000000 : ℝ) (130367069091/250000000000 : ℝ) (827569809271/1000000000000 : ℝ) (82756980929/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0568_exp_lower
  have heNumeric : (2019087042857/1000000000000 : ℝ)/4 ≤ Real.exp (-273459564341/400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019087042857/1000000000000 : ℝ)/4 ≤ Real.exp ((1179/8192 : ℝ)-(82756980929/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1179/8192 : ℝ) (295/2048 : ℝ) (82756980929/100000000000 : ℝ) (2019087042857/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0569; no trusted numerical premise.
theorem cover7_leaf0569_exp_radius : (997428935165826603/1000000000000000000 : ℝ) ≤ Real.exp ((-1181/57344 : ℝ)/8) ∧ Real.exp ((-1181/57344 : ℝ)/8) ≤ (249357233791456651/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1181/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0569_exp_lower : (918093949248247609/1000000000000000000 : ℝ) ≤ Real.exp ((-683644418953/1000000000000 : ℝ)/8) ∧ Real.exp ((-683644418953/1000000000000 : ℝ)/8) ≤ (91809394924824761/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683644418953/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0569_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019096112413/1000000000000 : ℝ) ≤ 4*Real.exp (295/2048 : ℝ)*Real.exp (-mu (radius 7 (1181/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019096112413/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1181/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0569_exp_radius
  have hrNumeric : (489807811551/500000000000 : ℝ) ≤ Real.exp (-1181/57344 : ℝ) ∧ Real.exp (-1181/57344 : ℝ) ≤ (979615623103/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (489807811551/500000000000 : ℝ) ≤ (radius 7 (1181/8192 : ℝ)) ∧ (radius 7 (1181/8192 : ℝ)) ≤ (979615623103/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1181/8192 : ℝ)) (489807811551/500000000000 : ℝ) (979615623103/1000000000000 : ℝ) (200881136427/1000000000000 : ℝ) (200881136433/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1181/8192 : ℝ)) (489807811551/500000000000 : ℝ) (979615623103/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1181/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (489807811551/500000000000 : ℝ) (979615623103/1000000000000 : ℝ) (989807811551/1000000000000 : ℝ) (30931494111/31250000000 : ℝ) (98975533497/100000000000 : ℝ) (989755334971/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1181/8192 : ℝ)) 1 (989807811551/1000000000000 : ℝ) (30931494111/31250000000 : ℝ) (98975533497/100000000000 : ℝ) (989755334971/1000000000000 : ℝ) (49489078663/50000000000 : ℝ) (494890786631/500000000000 : ℝ) (61861348307/62500000000 : ℝ) (494890786457/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1181/8192 : ℝ)) 2 (49489078663/50000000000 : ℝ) (494890786631/500000000000 : ℝ) (61861348307/62500000000 : ℝ) (494890786457/500000000000 : ℝ) (494890786543/500000000000 : ℝ) (30930674159/31250000000 : ℝ) (197956314617/200000000000 : ℝ) (30930674159/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1181/8192 : ℝ)) 3 (494890786543/500000000000 : ℝ) (30930674159/31250000000 : ℝ) (197956314617/200000000000 : ℝ) (30930674159/31250000000 : ℝ) (197956314617/200000000000 : ℝ) (30930674159/31250000000 : ℝ) (197956314617/200000000000 : ℝ) (30930674159/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1181/8192 : ℝ)) 4 (197956314617/200000000000 : ℝ) (30930674159/31250000000 : ℝ) (197956314617/200000000000 : ℝ) (30930674159/31250000000 : ℝ) (197956314617/200000000000 : ℝ) (30930674159/31250000000 : ℝ) (197956314617/200000000000 : ℝ) (30930674159/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1181/8192 : ℝ)) 5 (197956314617/200000000000 : ℝ) (30930674159/31250000000 : ℝ) (197956314617/200000000000 : ℝ) (30930674159/31250000000 : ℝ) (197956314617/200000000000 : ℝ) (30930674159/31250000000 : ℝ) (197956314617/200000000000 : ℝ) (30930674159/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1181/8192 : ℝ)) 6 (197956314617/200000000000 : ℝ) (30930674159/31250000000 : ℝ) (197956314617/200000000000 : ℝ) (30930674159/31250000000 : ℝ) (197956314617/200000000000 : ℝ) (30930674159/31250000000 : ℝ) (197956314617/200000000000 : ℝ) (30930674159/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1181/8192 : ℝ)) 7 (197956314617/200000000000 : ℝ) (30930674159/31250000000 : ℝ) (197956314617/200000000000 : ℝ) (30930674159/31250000000 : ℝ) (197956314617/200000000000 : ℝ) (30930674159/31250000000 : ℝ) (197956314617/200000000000 : ℝ) (30930674159/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1181/8192 : ℝ))) (200881136427/1000000000000 : ℝ) (200881136433/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1181/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (200881136427/1000000000000 : ℝ) (200881136433/1000000000000 : ℝ) (600440568213/1000000000000 : ℝ) (600440568217/1000000000000 : ℝ) (448197653303/1000000000000 : ℝ) (448197653311/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1181/8192 : ℝ))) 1 (600440568213/1000000000000 : ℝ) (600440568217/1000000000000 : ℝ) (448197653303/1000000000000 : ℝ) (448197653311/1000000000000 : ℝ) (262159555379/500000000000 : ℝ) (131079777691/250000000000 : ℝ) (518763967157/1000000000000 : ℝ) (129690991791/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1181/8192 : ℝ))) 2 (262159555379/500000000000 : ℝ) (131079777691/250000000000 : ℝ) (518763967157/1000000000000 : ℝ) (129690991791/250000000000 : ℝ) (521541538957/1000000000000 : ℝ) (130385384741/250000000000 : ℝ) (521534142653/1000000000000 : ℝ) (26076707133/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1181/8192 : ℝ))) 3 (521541538957/1000000000000 : ℝ) (130385384741/250000000000 : ℝ) (521534142653/1000000000000 : ℝ) (26076707133/50000000000 : ℝ) (104307568161/200000000000 : ℝ) (130384460203/250000000000 : ℝ) (521537840791/1000000000000 : ℝ) (521537840799/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1181/8192 : ℝ))) 4 (104307568161/200000000000 : ℝ) (130384460203/250000000000 : ℝ) (521537840791/1000000000000 : ℝ) (521537840799/1000000000000 : ℝ) (260768920399/500000000000 : ℝ) (260768920403/500000000000 : ℝ) (521537840797/1000000000000 : ℝ) (260768920403/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1181/8192 : ℝ))) 5 (260768920399/500000000000 : ℝ) (260768920403/500000000000 : ℝ) (521537840797/1000000000000 : ℝ) (260768920403/500000000000 : ℝ) (521537840797/1000000000000 : ℝ) (260768920403/500000000000 : ℝ) (521537840797/1000000000000 : ℝ) (260768920403/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1181/8192 : ℝ))) 6 (521537840797/1000000000000 : ℝ) (260768920403/500000000000 : ℝ) (521537840797/1000000000000 : ℝ) (260768920403/500000000000 : ℝ) (521537840797/1000000000000 : ℝ) (260768920403/500000000000 : ℝ) (521537840797/1000000000000 : ℝ) (260768920403/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1181/8192 : ℝ))) 7 (521537840797/1000000000000 : ℝ) (260768920403/500000000000 : ℝ) (521537840797/1000000000000 : ℝ) (260768920403/500000000000 : ℝ) (521537840797/1000000000000 : ℝ) (260768920403/500000000000 : ℝ) (521537840797/1000000000000 : ℝ) (260768920403/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1181/8192 : ℝ)) hmem 8 (197956314617/200000000000 : ℝ) (30930674159/31250000000 : ℝ) (197956314617/200000000000 : ℝ) (30930674159/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1181/8192 : ℝ))) hcmem 8 (521537840797/1000000000000 : ℝ) (260768920403/500000000000 : ℝ) (521537840797/1000000000000 : ℝ) (260768920403/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1181/8192 : ℝ)) (197956314617/200000000000 : ℝ) (30930674159/31250000000 : ℝ) (521537840797/1000000000000 : ℝ) (260768920403/500000000000 : ℝ) (165537477537/200000000000 : ℝ) (827687387703/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0569_exp_lower
  have heNumeric : (2019096112413/1000000000000 : ℝ)/4 ≤ Real.exp (-683644418953/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019096112413/1000000000000 : ℝ)/4 ≤ Real.exp ((295/2048 : ℝ)-(827687387703/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (295/2048 : ℝ) (1181/8192 : ℝ) (827687387703/1000000000000 : ℝ) (2019096112413/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0570; no trusted numerical premise.
theorem cover7_leaf0570_exp_radius : (498713380472831977/500000000000000000 : ℝ) ≤ Real.exp ((-591/28672 : ℝ)/8) ∧ Real.exp ((-591/28672 : ℝ)/8) ≤ (199485352189132791/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-591/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0570_exp_lower : (918094472337760631/1000000000000000000 : ℝ) ≤ Real.exp ((-1367279721813/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367279721813/2000000000000 : ℝ)/8) ≤ (114761809042220079/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367279721813/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0570_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (126194082223/62500000000 : ℝ) ≤ 4*Real.exp (1181/8192 : ℝ)*Real.exp (-mu (radius 7 (591/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (126194082223/62500000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (591/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0570_exp_radius
  have hrNumeric : (97959854011/100000000000 : ℝ) ≤ Real.exp (-591/28672 : ℝ) ∧ Real.exp (-591/28672 : ℝ) ≤ (979598540111/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (97959854011/100000000000 : ℝ) ≤ (radius 7 (591/4096 : ℝ)) ∧ (radius 7 (591/4096 : ℝ)) ≤ (979598540111/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (591/4096 : ℝ)) (97959854011/100000000000 : ℝ) (979598540111/1000000000000 : ℝ) (5024110631/25000000000 : ℝ) (100482212623/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (591/4096 : ℝ)) (97959854011/100000000000 : ℝ) (979598540111/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (591/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (97959854011/100000000000 : ℝ) (979598540111/1000000000000 : ℝ) (197959854011/200000000000 : ℝ) (123724908757/125000000000 : ℝ) (494873352513/500000000000 : ℝ) (989746705027/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (591/4096 : ℝ)) 1 (197959854011/200000000000 : ℝ) (123724908757/125000000000 : ℝ) (494873352513/500000000000 : ℝ) (989746705027/1000000000000 : ℝ) (49488649377/50000000000 : ℝ) (494886493771/500000000000 : ℝ) (989772987191/1000000000000 : ℝ) (989772987193/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (591/4096 : ℝ)) 2 (49488649377/50000000000 : ℝ) (494886493771/500000000000 : ℝ) (989772987191/1000000000000 : ℝ) (989772987193/1000000000000 : ℝ) (197954597473/200000000000 : ℝ) (123721623421/125000000000 : ℝ) (197954597473/200000000000 : ℝ) (123721623421/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (591/4096 : ℝ)) 3 (197954597473/200000000000 : ℝ) (123721623421/125000000000 : ℝ) (197954597473/200000000000 : ℝ) (123721623421/125000000000 : ℝ) (197954597473/200000000000 : ℝ) (123721623421/125000000000 : ℝ) (197954597473/200000000000 : ℝ) (123721623421/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (591/4096 : ℝ)) 4 (197954597473/200000000000 : ℝ) (123721623421/125000000000 : ℝ) (197954597473/200000000000 : ℝ) (123721623421/125000000000 : ℝ) (197954597473/200000000000 : ℝ) (123721623421/125000000000 : ℝ) (197954597473/200000000000 : ℝ) (123721623421/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (591/4096 : ℝ)) 5 (197954597473/200000000000 : ℝ) (123721623421/125000000000 : ℝ) (197954597473/200000000000 : ℝ) (123721623421/125000000000 : ℝ) (197954597473/200000000000 : ℝ) (123721623421/125000000000 : ℝ) (197954597473/200000000000 : ℝ) (123721623421/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (591/4096 : ℝ)) 6 (197954597473/200000000000 : ℝ) (123721623421/125000000000 : ℝ) (197954597473/200000000000 : ℝ) (123721623421/125000000000 : ℝ) (197954597473/200000000000 : ℝ) (123721623421/125000000000 : ℝ) (197954597473/200000000000 : ℝ) (123721623421/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (591/4096 : ℝ)) 7 (197954597473/200000000000 : ℝ) (123721623421/125000000000 : ℝ) (197954597473/200000000000 : ℝ) (123721623421/125000000000 : ℝ) (197954597473/200000000000 : ℝ) (123721623421/125000000000 : ℝ) (197954597473/200000000000 : ℝ) (123721623421/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (591/4096 : ℝ))) (5024110631/25000000000 : ℝ) (100482212623/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (591/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (5024110631/25000000000 : ℝ) (100482212623/500000000000 : ℝ) (30024110631/50000000000 : ℝ) (600482212623/1000000000000 : ℝ) (89658111789/200000000000 : ℝ) (448290558953/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (591/4096 : ℝ))) 1 (30024110631/50000000000 : ℝ) (600482212623/1000000000000 : ℝ) (89658111789/200000000000 : ℝ) (448290558953/1000000000000 : ℝ) (262193192891/500000000000 : ℝ) (131096596447/250000000000 : ℝ) (518835722297/1000000000000 : ℝ) (8106808161/15625000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (591/4096 : ℝ))) 2 (262193192891/500000000000 : ℝ) (131096596447/250000000000 : ℝ) (518835722297/1000000000000 : ℝ) (8106808161/15625000000 : ℝ) (521611054039/1000000000000 : ℝ) (260805527023/500000000000 : ℝ) (130400917661/250000000000 : ℝ) (130400917663/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (591/4096 : ℝ))) 3 (521611054039/1000000000000 : ℝ) (260805527023/500000000000 : ℝ) (130400917661/250000000000 : ℝ) (130400917663/250000000000 : ℝ) (521607362341/1000000000000 : ℝ) (521607362349/1000000000000 : ℝ) (65200920291/125000000000 : ℝ) (16300230073/31250000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (591/4096 : ℝ))) 4 (521607362341/1000000000000 : ℝ) (521607362349/1000000000000 : ℝ) (65200920291/125000000000 : ℝ) (16300230073/31250000000 : ℝ) (260803681167/500000000000 : ℝ) (521607362343/1000000000000 : ℝ) (260803681167/500000000000 : ℝ) (521607362343/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (591/4096 : ℝ))) 5 (260803681167/500000000000 : ℝ) (521607362343/1000000000000 : ℝ) (260803681167/500000000000 : ℝ) (521607362343/1000000000000 : ℝ) (260803681167/500000000000 : ℝ) (521607362343/1000000000000 : ℝ) (260803681167/500000000000 : ℝ) (521607362343/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (591/4096 : ℝ))) 6 (260803681167/500000000000 : ℝ) (521607362343/1000000000000 : ℝ) (260803681167/500000000000 : ℝ) (521607362343/1000000000000 : ℝ) (260803681167/500000000000 : ℝ) (521607362343/1000000000000 : ℝ) (260803681167/500000000000 : ℝ) (521607362343/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (591/4096 : ℝ))) 7 (260803681167/500000000000 : ℝ) (521607362343/1000000000000 : ℝ) (260803681167/500000000000 : ℝ) (521607362343/1000000000000 : ℝ) (260803681167/500000000000 : ℝ) (521607362343/1000000000000 : ℝ) (260803681167/500000000000 : ℝ) (521607362343/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (591/4096 : ℝ)) hmem 8 (197954597473/200000000000 : ℝ) (123721623421/125000000000 : ℝ) (197954597473/200000000000 : ℝ) (123721623421/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (591/4096 : ℝ))) hcmem 8 (260803681167/500000000000 : ℝ) (521607362343/1000000000000 : ℝ) (260803681167/500000000000 : ℝ) (521607362343/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (591/4096 : ℝ)) (197954597473/200000000000 : ℝ) (123721623421/125000000000 : ℝ) (260803681167/500000000000 : ℝ) (521607362343/1000000000000 : ℝ) (51737806247/62500000000 : ℝ) (827804899969/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0570_exp_lower
  have heNumeric : (126194082223/62500000000 : ℝ)/4 ≤ Real.exp (-1367279721813/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (126194082223/62500000000 : ℝ)/4 ≤ Real.exp ((1181/8192 : ℝ)-(827804899969/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1181/8192 : ℝ) (591/4096 : ℝ) (827804899969/1000000000000 : ℝ) (126194082223/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0571; no trusted numerical premise.
theorem cover7_leaf0571_exp_radius : (249356146682560181/250000000000000000 : ℝ) ≤ Real.exp ((-169/8192 : ℝ)/8) ∧ Real.exp ((-169/8192 : ℝ)/8) ≤ (39896983469209629/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-169/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0571_exp_lower : (459047501503624619/500000000000000000 : ℝ) ≤ Real.exp ((-683635236813/1000000000000 : ℝ)/8) ∧ Real.exp ((-683635236813/1000000000000 : ℝ)/8) ≤ (918095003007249239/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683635236813/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0571_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009557326061/500000000000 : ℝ) ≤ 4*Real.exp (591/4096 : ℝ)*Real.exp (-mu (radius 7 (1183/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (1009557326061/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1183/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0571_exp_radius
  have hrNumeric : (122447682177/125000000000 : ℝ) ≤ Real.exp (-169/8192 : ℝ) ∧ Real.exp (-169/8192 : ℝ) ≤ (979581457417/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122447682177/125000000000 : ℝ) ≤ (radius 7 (1183/8192 : ℝ)) ∧ (radius 7 (1183/8192 : ℝ)) ≤ (979581457417/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1183/8192 : ℝ)) (122447682177/125000000000 : ℝ) (979581457417/1000000000000 : ℝ) (100523838323/500000000000 : ℝ) (201047676651/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1183/8192 : ℝ)) (122447682177/125000000000 : ℝ) (979581457417/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1183/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122447682177/125000000000 : ℝ) (979581457417/1000000000000 : ℝ) (247447682177/250000000000 : ℝ) (989790728709/1000000000000 : ℝ) (989738075157/1000000000000 : ℝ) (494869037579/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1183/8192 : ℝ)) 1 (247447682177/250000000000 : ℝ) (989790728709/1000000000000 : ℝ) (989738075157/1000000000000 : ℝ) (494869037579/500000000000 : ℝ) (247441100483/250000000000 : ℝ) (494882200967/500000000000 : ℝ) (494882200791/500000000000 : ℝ) (61860275099/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1183/8192 : ℝ)) 2 (247441100483/250000000000 : ℝ) (494882200967/500000000000 : ℝ) (494882200791/500000000000 : ℝ) (61860275099/62500000000 : ℝ) (989764401757/1000000000000 : ℝ) (989764401759/1000000000000 : ℝ) (247441100439/250000000000 : ℝ) (989764401759/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1183/8192 : ℝ)) 3 (989764401757/1000000000000 : ℝ) (989764401759/1000000000000 : ℝ) (247441100439/250000000000 : ℝ) (989764401759/1000000000000 : ℝ) (247441100439/250000000000 : ℝ) (989764401759/1000000000000 : ℝ) (247441100439/250000000000 : ℝ) (989764401759/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1183/8192 : ℝ)) 4 (247441100439/250000000000 : ℝ) (989764401759/1000000000000 : ℝ) (247441100439/250000000000 : ℝ) (989764401759/1000000000000 : ℝ) (247441100439/250000000000 : ℝ) (989764401759/1000000000000 : ℝ) (247441100439/250000000000 : ℝ) (989764401759/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1183/8192 : ℝ)) 5 (247441100439/250000000000 : ℝ) (989764401759/1000000000000 : ℝ) (247441100439/250000000000 : ℝ) (989764401759/1000000000000 : ℝ) (247441100439/250000000000 : ℝ) (989764401759/1000000000000 : ℝ) (247441100439/250000000000 : ℝ) (989764401759/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1183/8192 : ℝ)) 6 (247441100439/250000000000 : ℝ) (989764401759/1000000000000 : ℝ) (247441100439/250000000000 : ℝ) (989764401759/1000000000000 : ℝ) (247441100439/250000000000 : ℝ) (989764401759/1000000000000 : ℝ) (247441100439/250000000000 : ℝ) (989764401759/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1183/8192 : ℝ)) 7 (247441100439/250000000000 : ℝ) (989764401759/1000000000000 : ℝ) (247441100439/250000000000 : ℝ) (989764401759/1000000000000 : ℝ) (247441100439/250000000000 : ℝ) (989764401759/1000000000000 : ℝ) (247441100439/250000000000 : ℝ) (989764401759/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1183/8192 : ℝ))) (100523838323/500000000000 : ℝ) (201047676651/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1183/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (100523838323/500000000000 : ℝ) (201047676651/1000000000000 : ℝ) (600523838323/1000000000000 : ℝ) (300261919163/500000000000 : ℝ) (56047925453/125000000000 : ℝ) (448383403631/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1183/8192 : ℝ))) 1 (600523838323/1000000000000 : ℝ) (300261919163/500000000000 : ℝ) (56047925453/125000000000 : ℝ) (448383403631/1000000000000 : ℝ) (524453620973/1000000000000 : ℝ) (524453620979/1000000000000 : ℝ) (259453715807/500000000000 : ℝ) (25945371581/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1183/8192 : ℝ))) 2 (524453620973/1000000000000 : ℝ) (524453620979/1000000000000 : ℝ) (259453715807/500000000000 : ℝ) (25945371581/50000000000 : ℝ) (521680526293/1000000000000 : ℝ) (5216805263/10000000000 : ℝ) (260836577889/500000000000 : ℝ) (104334631157/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1183/8192 : ℝ))) 3 (521680526293/1000000000000 : ℝ) (5216805263/10000000000 : ℝ) (260836577889/500000000000 : ℝ) (104334631157/200000000000 : ℝ) (104335368207/200000000000 : ℝ) (521676841043/1000000000000 : ℝ) (260838420511/500000000000 : ℝ) (52167684103/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1183/8192 : ℝ))) 4 (104335368207/200000000000 : ℝ) (521676841043/1000000000000 : ℝ) (260838420511/500000000000 : ℝ) (52167684103/100000000000 : ℝ) (130419210257/250000000000 : ℝ) (521676841037/1000000000000 : ℝ) (130419210257/250000000000 : ℝ) (521676841037/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1183/8192 : ℝ))) 5 (130419210257/250000000000 : ℝ) (521676841037/1000000000000 : ℝ) (130419210257/250000000000 : ℝ) (521676841037/1000000000000 : ℝ) (130419210257/250000000000 : ℝ) (521676841037/1000000000000 : ℝ) (130419210257/250000000000 : ℝ) (521676841037/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1183/8192 : ℝ))) 6 (130419210257/250000000000 : ℝ) (521676841037/1000000000000 : ℝ) (130419210257/250000000000 : ℝ) (521676841037/1000000000000 : ℝ) (130419210257/250000000000 : ℝ) (521676841037/1000000000000 : ℝ) (130419210257/250000000000 : ℝ) (521676841037/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1183/8192 : ℝ))) 7 (130419210257/250000000000 : ℝ) (521676841037/1000000000000 : ℝ) (130419210257/250000000000 : ℝ) (521676841037/1000000000000 : ℝ) (130419210257/250000000000 : ℝ) (521676841037/1000000000000 : ℝ) (130419210257/250000000000 : ℝ) (521676841037/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1183/8192 : ℝ)) hmem 8 (247441100439/250000000000 : ℝ) (989764401759/1000000000000 : ℝ) (247441100439/250000000000 : ℝ) (989764401759/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1183/8192 : ℝ))) hcmem 8 (130419210257/250000000000 : ℝ) (521676841037/1000000000000 : ℝ) (130419210257/250000000000 : ℝ) (521676841037/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1183/8192 : ℝ)) (247441100439/250000000000 : ℝ) (989764401759/1000000000000 : ℝ) (130419210257/250000000000 : ℝ) (521676841037/1000000000000 : ℝ) (82792234617/100000000000 : ℝ) (206980586547/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0571_exp_lower
  have heNumeric : (1009557326061/500000000000 : ℝ)/4 ≤ Real.exp (-683635236813/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009557326061/500000000000 : ℝ)/4 ≤ Real.exp ((591/4096 : ℝ)-(206980586547/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (591/4096 : ℝ) (1183/8192 : ℝ) (206980586547/250000000000 : ℝ) (1009557326061/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0572; no trusted numerical premise.
theorem cover7_leaf0572_exp_radius : (997422412519556903/1000000000000000000 : ℝ) ≤ Real.exp ((-37/1792 : ℝ)/8) ∧ Real.exp ((-37/1792 : ℝ)/8) ≤ (124677801564944613/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-37/1792 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0572_exp_lower : (918095541246283237/1000000000000000000 : ℝ) ≤ Real.exp ((-1367261093527/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367261093527/2000000000000 : ℝ)/8) ≤ (459047770623141619/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367261093527/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0572_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504781030473/250000000000 : ℝ) ≤ 4*Real.exp (1183/8192 : ℝ)*Real.exp (-mu (radius 7 (37/256 : ℝ))) ∧ (2019/1000 : ℝ) < (504781030473/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (37/256 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0572_exp_radius
  have hrNumeric : (48978218751/50000000000 : ℝ) ≤ Real.exp (-37/1792 : ℝ) ∧ Real.exp (-37/1792 : ℝ) ≤ (979564375021/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (48978218751/50000000000 : ℝ) ≤ (radius 7 (37/256 : ℝ)) ∧ (radius 7 (37/256 : ℝ)) ≤ (979564375021/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (37/256 : ℝ)) (48978218751/50000000000 : ℝ) (979564375021/1000000000000 : ℝ) (201130890689/1000000000000 : ℝ) (40226178139/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (37/256 : ℝ)) (48978218751/50000000000 : ℝ) (979564375021/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (37/256 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (48978218751/50000000000 : ℝ) (979564375021/1000000000000 : ℝ) (98978218751/100000000000 : ℝ) (989782187511/1000000000000 : ℝ) (989729445363/1000000000000 : ℝ) (197945889073/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (37/256 : ℝ)) 1 (98978218751/100000000000 : ℝ) (989782187511/1000000000000 : ℝ) (989729445363/1000000000000 : ℝ) (197945889073/200000000000 : ℝ) (247438954109/250000000000 : ℝ) (494877908219/500000000000 : ℝ) (197951163217/200000000000 : ℝ) (989755816087/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (37/256 : ℝ)) 2 (247438954109/250000000000 : ℝ) (494877908219/500000000000 : ℝ) (197951163217/200000000000 : ℝ) (989755816087/1000000000000 : ℝ) (49487790813/50000000000 : ℝ) (989755816263/1000000000000 : ℝ) (49487790813/50000000000 : ℝ) (989755816263/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (37/256 : ℝ)) 3 (49487790813/50000000000 : ℝ) (989755816263/1000000000000 : ℝ) (49487790813/50000000000 : ℝ) (989755816263/1000000000000 : ℝ) (49487790813/50000000000 : ℝ) (989755816263/1000000000000 : ℝ) (49487790813/50000000000 : ℝ) (989755816263/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (37/256 : ℝ)) 4 (49487790813/50000000000 : ℝ) (989755816263/1000000000000 : ℝ) (49487790813/50000000000 : ℝ) (989755816263/1000000000000 : ℝ) (49487790813/50000000000 : ℝ) (989755816263/1000000000000 : ℝ) (49487790813/50000000000 : ℝ) (989755816263/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (37/256 : ℝ)) 5 (49487790813/50000000000 : ℝ) (989755816263/1000000000000 : ℝ) (49487790813/50000000000 : ℝ) (989755816263/1000000000000 : ℝ) (49487790813/50000000000 : ℝ) (989755816263/1000000000000 : ℝ) (49487790813/50000000000 : ℝ) (989755816263/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (37/256 : ℝ)) 6 (49487790813/50000000000 : ℝ) (989755816263/1000000000000 : ℝ) (49487790813/50000000000 : ℝ) (989755816263/1000000000000 : ℝ) (49487790813/50000000000 : ℝ) (989755816263/1000000000000 : ℝ) (49487790813/50000000000 : ℝ) (989755816263/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (37/256 : ℝ)) 7 (49487790813/50000000000 : ℝ) (989755816263/1000000000000 : ℝ) (49487790813/50000000000 : ℝ) (989755816263/1000000000000 : ℝ) (49487790813/50000000000 : ℝ) (989755816263/1000000000000 : ℝ) (49487790813/50000000000 : ℝ) (989755816263/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (37/256 : ℝ))) (201130890689/1000000000000 : ℝ) (40226178139/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (37/256 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (201130890689/1000000000000 : ℝ) (40226178139/200000000000 : ℝ) (18767670167/31250000000 : ℝ) (150141361337/250000000000 : ℝ) (224238093713/500000000000 : ℝ) (224238093717/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (37/256 : ℝ))) 1 (18767670167/31250000000 : ℝ) (150141361337/250000000000 : ℝ) (224238093713/500000000000 : ℝ) (224238093717/500000000000 : ℝ) (104904163277/200000000000 : ℝ) (524520816391/1000000000000 : ℝ) (259489547587/500000000000 : ℝ) (518979095181/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (37/256 : ℝ))) 2 (104904163277/200000000000 : ℝ) (524520816391/1000000000000 : ℝ) (259489547587/500000000000 : ℝ) (518979095181/1000000000000 : ℝ) (521749955779/1000000000000 : ℝ) (260874977893/500000000000 : ℝ) (260871299057/500000000000 : ℝ) (260871299061/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (37/256 : ℝ))) 3 (521749955779/1000000000000 : ℝ) (260874977893/500000000000 : ℝ) (260871299057/500000000000 : ℝ) (260871299061/500000000000 : ℝ) (260873138473/500000000000 : ℝ) (260873138477/500000000000 : ℝ) (521746276933/1000000000000 : ℝ) (260873138471/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (37/256 : ℝ))) 4 (260873138473/500000000000 : ℝ) (260873138477/500000000000 : ℝ) (521746276933/1000000000000 : ℝ) (260873138471/500000000000 : ℝ) (521746276939/1000000000000 : ℝ) (130436569237/250000000000 : ℝ) (521746276939/1000000000000 : ℝ) (130436569237/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (37/256 : ℝ))) 5 (521746276939/1000000000000 : ℝ) (130436569237/250000000000 : ℝ) (521746276939/1000000000000 : ℝ) (130436569237/250000000000 : ℝ) (521746276939/1000000000000 : ℝ) (130436569237/250000000000 : ℝ) (521746276939/1000000000000 : ℝ) (130436569237/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (37/256 : ℝ))) 6 (521746276939/1000000000000 : ℝ) (130436569237/250000000000 : ℝ) (521746276939/1000000000000 : ℝ) (130436569237/250000000000 : ℝ) (521746276939/1000000000000 : ℝ) (130436569237/250000000000 : ℝ) (521746276939/1000000000000 : ℝ) (130436569237/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (37/256 : ℝ))) 7 (521746276939/1000000000000 : ℝ) (130436569237/250000000000 : ℝ) (521746276939/1000000000000 : ℝ) (130436569237/250000000000 : ℝ) (521746276939/1000000000000 : ℝ) (130436569237/250000000000 : ℝ) (521746276939/1000000000000 : ℝ) (130436569237/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (37/256 : ℝ)) hmem 8 (49487790813/50000000000 : ℝ) (989755816263/1000000000000 : ℝ) (49487790813/50000000000 : ℝ) (989755816263/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (37/256 : ℝ))) hcmem 8 (521746276939/1000000000000 : ℝ) (130436569237/250000000000 : ℝ) (521746276939/1000000000000 : ℝ) (130436569237/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (37/256 : ℝ)) (49487790813/50000000000 : ℝ) (989755816263/1000000000000 : ℝ) (521746276939/1000000000000 : ℝ) (130436569237/250000000000 : ℝ) (828039726433/1000000000000 : ℝ) (828039726451/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0572_exp_lower
  have heNumeric : (504781030473/250000000000 : ℝ)/4 ≤ Real.exp (-1367261093527/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504781030473/250000000000 : ℝ)/4 ≤ Real.exp ((1183/8192 : ℝ)-(828039726451/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1183/8192 : ℝ) (37/256 : ℝ) (828039726451/1000000000000 : ℝ) (504781030473/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0573; no trusted numerical premise.
theorem cover7_leaf0573_exp_radius : (997420238313612479/1000000000000000000 : ℝ) ≤ Real.exp ((-1185/57344 : ℝ)/8) ∧ Real.exp ((-1185/57344 : ℝ)/8) ≤ (3116938244730039/3125000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1185/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0573_exp_lower : (183619217408634043/200000000000000000 : ℝ) ≤ Real.exp ((-34181289543/50000000000 : ℝ)/8) ∧ Real.exp ((-34181289543/50000000000 : ℝ)/8) ≤ (114762010880396277/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-34181289543/50000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0573_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009566862337/500000000000 : ℝ) ≤ 4*Real.exp (37/256 : ℝ)*Real.exp (-mu (radius 7 (1185/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (1009566862337/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1185/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0573_exp_radius
  have hrNumeric : (489773646461/500000000000 : ℝ) ≤ Real.exp (-1185/57344 : ℝ) ∧ Real.exp (-1185/57344 : ℝ) ≤ (979547292923/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (489773646461/500000000000 : ℝ) ≤ (radius 7 (1185/8192 : ℝ)) ∧ (radius 7 (1185/8192 : ℝ)) ≤ (979547292923/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1185/8192 : ℝ)) (489773646461/500000000000 : ℝ) (979547292923/1000000000000 : ℝ) (100607033709/500000000000 : ℝ) (6287939607/31250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1185/8192 : ℝ)) (489773646461/500000000000 : ℝ) (979547292923/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1185/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (489773646461/500000000000 : ℝ) (979547292923/1000000000000 : ℝ) (989773646461/1000000000000 : ℝ) (494886823231/500000000000 : ℝ) (197944163129/200000000000 : ℝ) (989720815647/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1185/8192 : ℝ)) 1 (989773646461/1000000000000 : ℝ) (494886823231/500000000000 : ℝ) (197944163129/200000000000 : ℝ) (989720815647/1000000000000 : ℝ) (989747231053/1000000000000 : ℝ) (197949446211/200000000000 : ℝ) (9897472307/10000000000 : ℝ) (494873615351/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1185/8192 : ℝ)) 2 (989747231053/1000000000000 : ℝ) (197949446211/200000000000 : ℝ) (9897472307/10000000000 : ℝ) (494873615351/500000000000 : ℝ) (247436807719/250000000000 : ℝ) (989747230879/1000000000000 : ℝ) (247436807719/250000000000 : ℝ) (989747230879/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1185/8192 : ℝ)) 3 (247436807719/250000000000 : ℝ) (989747230879/1000000000000 : ℝ) (247436807719/250000000000 : ℝ) (989747230879/1000000000000 : ℝ) (247436807719/250000000000 : ℝ) (989747230879/1000000000000 : ℝ) (247436807719/250000000000 : ℝ) (989747230879/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1185/8192 : ℝ)) 4 (247436807719/250000000000 : ℝ) (989747230879/1000000000000 : ℝ) (247436807719/250000000000 : ℝ) (989747230879/1000000000000 : ℝ) (247436807719/250000000000 : ℝ) (989747230879/1000000000000 : ℝ) (247436807719/250000000000 : ℝ) (989747230879/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1185/8192 : ℝ)) 5 (247436807719/250000000000 : ℝ) (989747230879/1000000000000 : ℝ) (247436807719/250000000000 : ℝ) (989747230879/1000000000000 : ℝ) (247436807719/250000000000 : ℝ) (989747230879/1000000000000 : ℝ) (247436807719/250000000000 : ℝ) (989747230879/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1185/8192 : ℝ)) 6 (247436807719/250000000000 : ℝ) (989747230879/1000000000000 : ℝ) (247436807719/250000000000 : ℝ) (989747230879/1000000000000 : ℝ) (247436807719/250000000000 : ℝ) (989747230879/1000000000000 : ℝ) (247436807719/250000000000 : ℝ) (989747230879/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1185/8192 : ℝ)) 7 (247436807719/250000000000 : ℝ) (989747230879/1000000000000 : ℝ) (247436807719/250000000000 : ℝ) (989747230879/1000000000000 : ℝ) (247436807719/250000000000 : ℝ) (989747230879/1000000000000 : ℝ) (247436807719/250000000000 : ℝ) (989747230879/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1185/8192 : ℝ))) (100607033709/500000000000 : ℝ) (6287939607/31250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1185/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (100607033709/500000000000 : ℝ) (6287939607/31250000000 : ℝ) (600607033709/1000000000000 : ℝ) (37537939607/62500000000 : ℝ) (89713782089/200000000000 : ℝ) (112142227613/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1185/8192 : ℝ))) 1 (600607033709/1000000000000 : ℝ) (37537939607/62500000000 : ℝ) (89713782089/200000000000 : ℝ) (112142227613/250000000000 : ℝ) (524587972077/1000000000000 : ℝ) (262293986041/500000000000 : ℝ) (64881339131/125000000000 : ℝ) (103810142611/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1185/8192 : ℝ))) 2 (524587972077/1000000000000 : ℝ) (262293986041/500000000000 : ℝ) (64881339131/125000000000 : ℝ) (103810142611/200000000000 : ℝ) (260909671281/500000000000 : ℝ) (521819342569/1000000000000 : ℝ) (260905998859/500000000000 : ℝ) (20872479909/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1185/8192 : ℝ))) 3 (260909671281/500000000000 : ℝ) (521819342569/1000000000000 : ℝ) (260905998859/500000000000 : ℝ) (20872479909/40000000000 : ℝ) (26090783507/50000000000 : ℝ) (521815670147/1000000000000 : ℝ) (521815670127/1000000000000 : ℝ) (104363134027/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1185/8192 : ℝ))) 4 (26090783507/50000000000 : ℝ) (521815670147/1000000000000 : ℝ) (521815670127/1000000000000 : ℝ) (104363134027/200000000000 : ℝ) (521815670133/1000000000000 : ℝ) (521815670141/1000000000000 : ℝ) (521815670133/1000000000000 : ℝ) (521815670141/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1185/8192 : ℝ))) 5 (521815670133/1000000000000 : ℝ) (521815670141/1000000000000 : ℝ) (521815670133/1000000000000 : ℝ) (521815670141/1000000000000 : ℝ) (521815670133/1000000000000 : ℝ) (521815670141/1000000000000 : ℝ) (521815670133/1000000000000 : ℝ) (521815670141/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1185/8192 : ℝ))) 6 (521815670133/1000000000000 : ℝ) (521815670141/1000000000000 : ℝ) (521815670133/1000000000000 : ℝ) (521815670141/1000000000000 : ℝ) (521815670133/1000000000000 : ℝ) (521815670141/1000000000000 : ℝ) (521815670133/1000000000000 : ℝ) (521815670141/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1185/8192 : ℝ))) 7 (521815670133/1000000000000 : ℝ) (521815670141/1000000000000 : ℝ) (521815670133/1000000000000 : ℝ) (521815670141/1000000000000 : ℝ) (521815670133/1000000000000 : ℝ) (521815670141/1000000000000 : ℝ) (521815670133/1000000000000 : ℝ) (521815670141/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1185/8192 : ℝ)) hmem 8 (247436807719/250000000000 : ℝ) (989747230879/1000000000000 : ℝ) (247436807719/250000000000 : ℝ) (989747230879/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1185/8192 : ℝ))) hcmem 8 (521815670133/1000000000000 : ℝ) (521815670141/1000000000000 : ℝ) (521815670133/1000000000000 : ℝ) (521815670141/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1185/8192 : ℝ)) (247436807719/250000000000 : ℝ) (989747230879/1000000000000 : ℝ) (521815670133/1000000000000 : ℝ) (521815670141/1000000000000 : ℝ) (207039260211/250000000000 : ℝ) (41407852043/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0573_exp_lower
  have heNumeric : (1009566862337/500000000000 : ℝ)/4 ≤ Real.exp (-34181289543/50000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009566862337/500000000000 : ℝ)/4 ≤ Real.exp ((37/256 : ℝ)-(41407852043/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (37/256 : ℝ) (1185/8192 : ℝ) (41407852043/50000000000 : ℝ) (1009566862337/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0574; no trusted numerical premise.
theorem cover7_leaf0574_exp_radius : (997418064112407443/1000000000000000000 : ℝ) ≤ Real.exp ((-593/28672 : ℝ)/8) ∧ Real.exp ((-593/28672 : ℝ)/8) ≤ (249354516028101861/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-593/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0574_exp_lower : (91809664038679173/100000000000000000 : ℝ) ≤ Real.exp ((-1367241938399/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367241938399/2000000000000 : ℝ)/8) ≤ (918096640386791731/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367241938399/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0574_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (80765738411/40000000000 : ℝ) ≤ 4*Real.exp (1185/8192 : ℝ)*Real.exp (-mu (radius 7 (593/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (80765738411/40000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (593/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0574_exp_radius
  have hrNumeric : (489765105561/500000000000 : ℝ) ≤ Real.exp (-593/28672 : ℝ) ∧ Real.exp (-593/28672 : ℝ) ≤ (979530211123/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (489765105561/500000000000 : ℝ) ≤ (radius 7 (593/4096 : ℝ)) ∧ (radius 7 (593/4096 : ℝ)) ≤ (979530211123/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (593/4096 : ℝ)) (489765105561/500000000000 : ℝ) (979530211123/1000000000000 : ℝ) (201297206879/1000000000000 : ℝ) (50324301721/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (593/4096 : ℝ)) (489765105561/500000000000 : ℝ) (979530211123/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (593/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (489765105561/500000000000 : ℝ) (979530211123/1000000000000 : ℝ) (989765105561/1000000000000 : ℝ) (494882552781/500000000000 : ℝ) (494856093001/500000000000 : ℝ) (247428046501/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (593/4096 : ℝ)) 1 (989765105561/1000000000000 : ℝ) (494882552781/500000000000 : ℝ) (494856093001/500000000000 : ℝ) (247428046501/250000000000 : ℝ) (989738645781/1000000000000 : ℝ) (989738645783/1000000000000 : ℝ) (989738645427/1000000000000 : ℝ) (98973864543/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (593/4096 : ℝ)) 2 (989738645781/1000000000000 : ℝ) (989738645783/1000000000000 : ℝ) (989738645427/1000000000000 : ℝ) (98973864543/100000000000 : ℝ) (247434661401/250000000000 : ℝ) (989738645607/1000000000000 : ℝ) (989738645603/1000000000000 : ℝ) (989738645607/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (593/4096 : ℝ)) 3 (247434661401/250000000000 : ℝ) (989738645607/1000000000000 : ℝ) (989738645603/1000000000000 : ℝ) (989738645607/1000000000000 : ℝ) (989738645603/1000000000000 : ℝ) (989738645607/1000000000000 : ℝ) (989738645603/1000000000000 : ℝ) (989738645607/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (593/4096 : ℝ)) 4 (989738645603/1000000000000 : ℝ) (989738645607/1000000000000 : ℝ) (989738645603/1000000000000 : ℝ) (989738645607/1000000000000 : ℝ) (989738645603/1000000000000 : ℝ) (989738645607/1000000000000 : ℝ) (989738645603/1000000000000 : ℝ) (989738645607/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (593/4096 : ℝ)) 5 (989738645603/1000000000000 : ℝ) (989738645607/1000000000000 : ℝ) (989738645603/1000000000000 : ℝ) (989738645607/1000000000000 : ℝ) (989738645603/1000000000000 : ℝ) (989738645607/1000000000000 : ℝ) (989738645603/1000000000000 : ℝ) (989738645607/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (593/4096 : ℝ)) 6 (989738645603/1000000000000 : ℝ) (989738645607/1000000000000 : ℝ) (989738645603/1000000000000 : ℝ) (989738645607/1000000000000 : ℝ) (989738645603/1000000000000 : ℝ) (989738645607/1000000000000 : ℝ) (989738645603/1000000000000 : ℝ) (989738645607/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (593/4096 : ℝ)) 7 (989738645603/1000000000000 : ℝ) (989738645607/1000000000000 : ℝ) (989738645603/1000000000000 : ℝ) (989738645607/1000000000000 : ℝ) (989738645603/1000000000000 : ℝ) (989738645607/1000000000000 : ℝ) (989738645603/1000000000000 : ℝ) (989738645607/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (593/4096 : ℝ))) (201297206879/1000000000000 : ℝ) (50324301721/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (593/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (201297206879/1000000000000 : ℝ) (50324301721/250000000000 : ℝ) (600648603439/1000000000000 : ℝ) (300324301721/500000000000 : ℝ) (14020674149/31250000000 : ℝ) (224330786387/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (593/4096 : ℝ))) 1 (600648603439/1000000000000 : ℝ) (300324301721/500000000000 : ℝ) (14020674149/31250000000 : ℝ) (224330786387/500000000000 : ℝ) (524655088103/1000000000000 : ℝ) (131163772027/250000000000 : ℝ) (64890285663/125000000000 : ℝ) (51912228531/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (593/4096 : ℝ))) 2 (524655088103/1000000000000 : ℝ) (131163772027/250000000000 : ℝ) (64890285663/125000000000 : ℝ) (51912228531/100000000000 : ℝ) (521888686703/1000000000000 : ℝ) (521888686709/1000000000000 : ℝ) (521881354651/1000000000000 : ℝ) (521881354657/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (593/4096 : ℝ))) 3 (521888686703/1000000000000 : ℝ) (521888686709/1000000000000 : ℝ) (521881354651/1000000000000 : ℝ) (521881354657/1000000000000 : ℝ) (521885020677/1000000000000 : ℝ) (521885020683/1000000000000 : ℝ) (65235627583/125000000000 : ℝ) (521885020671/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (593/4096 : ℝ))) 4 (521885020677/1000000000000 : ℝ) (521885020683/1000000000000 : ℝ) (65235627583/125000000000 : ℝ) (521885020671/1000000000000 : ℝ) (52188502067/100000000000 : ℝ) (521885020677/1000000000000 : ℝ) (52188502067/100000000000 : ℝ) (521885020677/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (593/4096 : ℝ))) 5 (52188502067/100000000000 : ℝ) (521885020677/1000000000000 : ℝ) (52188502067/100000000000 : ℝ) (521885020677/1000000000000 : ℝ) (52188502067/100000000000 : ℝ) (521885020677/1000000000000 : ℝ) (52188502067/100000000000 : ℝ) (521885020677/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (593/4096 : ℝ))) 6 (52188502067/100000000000 : ℝ) (521885020677/1000000000000 : ℝ) (52188502067/100000000000 : ℝ) (521885020677/1000000000000 : ℝ) (52188502067/100000000000 : ℝ) (521885020677/1000000000000 : ℝ) (52188502067/100000000000 : ℝ) (521885020677/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (593/4096 : ℝ))) 7 (52188502067/100000000000 : ℝ) (521885020677/1000000000000 : ℝ) (52188502067/100000000000 : ℝ) (521885020677/1000000000000 : ℝ) (52188502067/100000000000 : ℝ) (521885020677/1000000000000 : ℝ) (52188502067/100000000000 : ℝ) (521885020677/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (593/4096 : ℝ)) hmem 8 (989738645603/1000000000000 : ℝ) (989738645607/1000000000000 : ℝ) (989738645603/1000000000000 : ℝ) (989738645607/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (593/4096 : ℝ))) hcmem 8 (52188502067/100000000000 : ℝ) (521885020677/1000000000000 : ℝ) (52188502067/100000000000 : ℝ) (521885020677/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (593/4096 : ℝ)) (989738645603/1000000000000 : ℝ) (989738645607/1000000000000 : ℝ) (52188502067/100000000000 : ℝ) (521885020677/1000000000000 : ℝ) (103534286187/125000000000 : ℝ) (103534286189/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0574_exp_lower
  have heNumeric : (80765738411/40000000000 : ℝ)/4 ≤ Real.exp (-1367241938399/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (80765738411/40000000000 : ℝ)/4 ≤ Real.exp ((1185/8192 : ℝ)-(103534286189/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1185/8192 : ℝ) (593/4096 : ℝ) (103534286189/125000000000 : ℝ) (80765738411/40000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_leaf0550_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0550_certificate
#check SmaleRate.Proofs.cover7_leaf0551_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0551_certificate
#check SmaleRate.Proofs.cover7_leaf0552_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0552_certificate
#check SmaleRate.Proofs.cover7_leaf0553_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0553_certificate
#check SmaleRate.Proofs.cover7_leaf0554_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0554_certificate
#check SmaleRate.Proofs.cover7_leaf0555_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0555_certificate
#check SmaleRate.Proofs.cover7_leaf0556_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0556_certificate
#check SmaleRate.Proofs.cover7_leaf0557_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0557_certificate
#check SmaleRate.Proofs.cover7_leaf0558_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0558_certificate
#check SmaleRate.Proofs.cover7_leaf0559_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0559_certificate
#check SmaleRate.Proofs.cover7_leaf0560_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0560_certificate
#check SmaleRate.Proofs.cover7_leaf0561_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0561_certificate
#check SmaleRate.Proofs.cover7_leaf0562_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0562_certificate
#check SmaleRate.Proofs.cover7_leaf0563_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0563_certificate
#check SmaleRate.Proofs.cover7_leaf0564_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0564_certificate
#check SmaleRate.Proofs.cover7_leaf0565_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0565_certificate
#check SmaleRate.Proofs.cover7_leaf0566_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0566_certificate
#check SmaleRate.Proofs.cover7_leaf0567_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0567_certificate
#check SmaleRate.Proofs.cover7_leaf0568_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0568_certificate
#check SmaleRate.Proofs.cover7_leaf0569_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0569_certificate
#check SmaleRate.Proofs.cover7_leaf0570_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0570_certificate
#check SmaleRate.Proofs.cover7_leaf0571_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0571_certificate
#check SmaleRate.Proofs.cover7_leaf0572_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0572_certificate
#check SmaleRate.Proofs.cover7_leaf0573_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0573_certificate
#check SmaleRate.Proofs.cover7_leaf0574_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0574_certificate
