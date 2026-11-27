/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf1575; no trusted numerical premise.
theorem cover8_leaf1575_exp_radius : (49897704007924973/50000000000000000 : ℝ) ≤ Real.exp ((-4295/262144 : ℝ)/8) ∧ Real.exp ((-4295/262144 : ℝ)/8) ≤ (997954080158499461/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4295/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1575_exp_lower : (115014206569750827/125000000000000000 : ℝ) ≤ Real.exp ((-2664258597753/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664258597753/4000000000000 : ℝ)/8) ≤ (920113652558006617/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664258597753/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1575_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054905192159/1000000000000 : ℝ) ≤ 4*Real.exp (2147/16384 : ℝ)*Real.exp (-mu (radius 8 (4295/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054905192159/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4295/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1575_exp_radius
  have hrNumeric : (122968670623/125000000000 : ℝ) ≤ Real.exp (-4295/262144 : ℝ) ∧ Real.exp (-4295/262144 : ℝ) ≤ (196749872997/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122968670623/125000000000 : ℝ) ≤ (radius 8 (4295/32768 : ℝ)) ∧ (radius 8 (4295/32768 : ℝ)) ≤ (196749872997/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4295/32768 : ℝ)) (122968670623/125000000000 : ℝ) (196749872997/200000000000 : ℝ) (44886792943/250000000000 : ℝ) (179547171779/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4295/32768 : ℝ)) (122968670623/125000000000 : ℝ) (196749872997/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4295/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122968670623/125000000000 : ℝ) (196749872997/200000000000 : ℝ) (247968670623/250000000000 : ℝ) (991874682493/1000000000000 : ℝ) (247960350281/250000000000 : ℝ) (7934731209/8000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4295/32768 : ℝ)) 1 (247968670623/250000000000 : ℝ) (991874682493/1000000000000 : ℝ) (247960350281/250000000000 : ℝ) (7934731209/8000000000 : ℝ) (61991127613/62500000000 : ℝ) (991858041809/1000000000000 : ℝ) (247964510417/250000000000 : ℝ) (99185804167/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4295/32768 : ℝ)) 2 (61991127613/62500000000 : ℝ) (991858041809/1000000000000 : ℝ) (247964510417/250000000000 : ℝ) (99185804167/100000000000 : ℝ) (495929020869/500000000000 : ℝ) (49592902087/50000000000 : ℝ) (991858041737/1000000000000 : ℝ) (49592902087/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4295/32768 : ℝ)) 3 (495929020869/500000000000 : ℝ) (49592902087/50000000000 : ℝ) (991858041737/1000000000000 : ℝ) (49592902087/50000000000 : ℝ) (991858041737/1000000000000 : ℝ) (49592902087/50000000000 : ℝ) (991858041737/1000000000000 : ℝ) (49592902087/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4295/32768 : ℝ)) 4 (991858041737/1000000000000 : ℝ) (49592902087/50000000000 : ℝ) (991858041737/1000000000000 : ℝ) (49592902087/50000000000 : ℝ) (991858041737/1000000000000 : ℝ) (49592902087/50000000000 : ℝ) (991858041737/1000000000000 : ℝ) (49592902087/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4295/32768 : ℝ)) 5 (991858041737/1000000000000 : ℝ) (49592902087/50000000000 : ℝ) (991858041737/1000000000000 : ℝ) (49592902087/50000000000 : ℝ) (991858041737/1000000000000 : ℝ) (49592902087/50000000000 : ℝ) (991858041737/1000000000000 : ℝ) (49592902087/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4295/32768 : ℝ)) 6 (991858041737/1000000000000 : ℝ) (49592902087/50000000000 : ℝ) (991858041737/1000000000000 : ℝ) (49592902087/50000000000 : ℝ) (991858041737/1000000000000 : ℝ) (49592902087/50000000000 : ℝ) (991858041737/1000000000000 : ℝ) (49592902087/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4295/32768 : ℝ)) 7 (991858041737/1000000000000 : ℝ) (49592902087/50000000000 : ℝ) (991858041737/1000000000000 : ℝ) (49592902087/50000000000 : ℝ) (991858041737/1000000000000 : ℝ) (49592902087/50000000000 : ℝ) (991858041737/1000000000000 : ℝ) (49592902087/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4295/32768 : ℝ))) (44886792943/250000000000 : ℝ) (179547171779/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4295/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44886792943/250000000000 : ℝ) (179547171779/1000000000000 : ℝ) (294886792943/500000000000 : ℝ) (58977358589/100000000000 : ℝ) (105932517367/250000000000 : ℝ) (211865034739/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4295/32768 : ℝ))) 1 (294886792943/500000000000 : ℝ) (58977358589/100000000000 : ℝ) (105932517367/250000000000 : ℝ) (211865034739/500000000000 : ℝ) (506751827677/1000000000000 : ℝ) (126687956921/250000000000 : ℝ) (499904793453/1000000000000 : ℝ) (249952396731/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4295/32768 : ℝ))) 2 (506751827677/1000000000000 : ℝ) (126687956921/250000000000 : ℝ) (499904793453/1000000000000 : ℝ) (249952396731/500000000000 : ℝ) (100665662113/200000000000 : ℝ) (503328310573/1000000000000 : ℝ) (503316667463/1000000000000 : ℝ) (31457291717/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4295/32768 : ℝ))) 3 (100665662113/200000000000 : ℝ) (503328310573/1000000000000 : ℝ) (503316667463/1000000000000 : ℝ) (31457291717/62500000000 : ℝ) (251661244507/500000000000 : ℝ) (503322489023/1000000000000 : ℝ) (25166124449/50000000000 : ℝ) (503322488989/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4295/32768 : ℝ))) 4 (251661244507/500000000000 : ℝ) (503322489023/1000000000000 : ℝ) (25166124449/50000000000 : ℝ) (503322488989/1000000000000 : ℝ) (503322488997/1000000000000 : ℝ) (251661244503/500000000000 : ℝ) (125830622249/250000000000 : ℝ) (251661244503/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4295/32768 : ℝ))) 5 (503322488997/1000000000000 : ℝ) (251661244503/500000000000 : ℝ) (125830622249/250000000000 : ℝ) (251661244503/500000000000 : ℝ) (125830622249/250000000000 : ℝ) (251661244503/500000000000 : ℝ) (125830622249/250000000000 : ℝ) (251661244503/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4295/32768 : ℝ))) 6 (125830622249/250000000000 : ℝ) (251661244503/500000000000 : ℝ) (125830622249/250000000000 : ℝ) (251661244503/500000000000 : ℝ) (125830622249/250000000000 : ℝ) (251661244503/500000000000 : ℝ) (125830622249/250000000000 : ℝ) (251661244503/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4295/32768 : ℝ))) 7 (125830622249/250000000000 : ℝ) (251661244503/500000000000 : ℝ) (125830622249/250000000000 : ℝ) (251661244503/500000000000 : ℝ) (125830622249/250000000000 : ℝ) (251661244503/500000000000 : ℝ) (125830622249/250000000000 : ℝ) (251661244503/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4295/32768 : ℝ)) hmem 8 (991858041737/1000000000000 : ℝ) (49592902087/50000000000 : ℝ) (991858041737/1000000000000 : ℝ) (49592902087/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4295/32768 : ℝ))) hcmem 8 (125830622249/250000000000 : ℝ) (251661244503/500000000000 : ℝ) (125830622249/250000000000 : ℝ) (251661244503/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4295/32768 : ℝ)) (991858041737/1000000000000 : ℝ) (49592902087/50000000000 : ℝ) (125830622249/250000000000 : ℝ) (251661244503/500000000000 : ℝ) (24909597809/31250000000 : ℝ) (797107129907/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1575_exp_lower
  have heNumeric : (2054905192159/1000000000000 : ℝ)/4 ≤ Real.exp (-2664258597753/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054905192159/1000000000000 : ℝ)/4 ≤ Real.exp ((2147/16384 : ℝ)-(797107129907/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2147/16384 : ℝ) (4295/32768 : ℝ) (797107129907/1000000000000 : ℝ) (2054905192159/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1576; no trusted numerical premise.
theorem cover8_leaf1576_exp_radius : (498976802148512657/500000000000000000 : ℝ) ≤ Real.exp ((-537/32768 : ℝ)/8) ∧ Real.exp ((-537/32768 : ℝ)/8) ≤ (199590720859405063/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-537/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1576_exp_lower : (920113714944489093/1000000000000000000 : ℝ) ≤ Real.exp ((-5328512856113/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328512856113/8000000000000 : ℝ)/8) ≤ (460056857472244547/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328512856113/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1576_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054906306789/1000000000000 : ℝ) ≤ 4*Real.exp (4295/32768 : ℝ)*Real.exp (-mu (radius 8 (537/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (2054906306789/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (537/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1576_exp_radius
  have hrNumeric : (196749122457/200000000000 : ℝ) ≤ Real.exp (-537/32768 : ℝ) ∧ Real.exp (-537/32768 : ℝ) ≤ (491872806143/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196749122457/200000000000 : ℝ) ≤ (radius 8 (537/4096 : ℝ)) ∧ (radius 8 (537/4096 : ℝ)) ≤ (491872806143/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (537/4096 : ℝ)) (196749122457/200000000000 : ℝ) (491872806143/500000000000 : ℝ) (179567731811/1000000000000 : ℝ) (89783865909/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (537/4096 : ℝ)) (196749122457/200000000000 : ℝ) (491872806143/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (537/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196749122457/200000000000 : ℝ) (491872806143/500000000000 : ℝ) (495936403071/500000000000 : ℝ) (991872806143/1000000000000 : ℝ) (495919754669/500000000000 : ℝ) (49591975467/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (537/4096 : ℝ)) 1 (495936403071/500000000000 : ℝ) (991872806143/1000000000000 : ℝ) (495919754669/500000000000 : ℝ) (49591975467/50000000000 : ℝ) (49592807887/50000000000 : ℝ) (495928078871/500000000000 : ℝ) (1239820197/1250000000 : ℝ) (495928078801/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (537/4096 : ℝ)) 2 (49592807887/50000000000 : ℝ) (495928078871/500000000000 : ℝ) (1239820197/1250000000 : ℝ) (495928078801/500000000000 : ℝ) (99185615767/100000000000 : ℝ) (123982019709/125000000000 : ℝ) (991856157669/1000000000000 : ℝ) (123982019709/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (537/4096 : ℝ)) 3 (99185615767/100000000000 : ℝ) (123982019709/125000000000 : ℝ) (991856157669/1000000000000 : ℝ) (123982019709/125000000000 : ℝ) (991856157669/1000000000000 : ℝ) (123982019709/125000000000 : ℝ) (991856157669/1000000000000 : ℝ) (123982019709/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (537/4096 : ℝ)) 4 (991856157669/1000000000000 : ℝ) (123982019709/125000000000 : ℝ) (991856157669/1000000000000 : ℝ) (123982019709/125000000000 : ℝ) (991856157669/1000000000000 : ℝ) (123982019709/125000000000 : ℝ) (991856157669/1000000000000 : ℝ) (123982019709/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (537/4096 : ℝ)) 5 (991856157669/1000000000000 : ℝ) (123982019709/125000000000 : ℝ) (991856157669/1000000000000 : ℝ) (123982019709/125000000000 : ℝ) (991856157669/1000000000000 : ℝ) (123982019709/125000000000 : ℝ) (991856157669/1000000000000 : ℝ) (123982019709/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (537/4096 : ℝ)) 6 (991856157669/1000000000000 : ℝ) (123982019709/125000000000 : ℝ) (991856157669/1000000000000 : ℝ) (123982019709/125000000000 : ℝ) (991856157669/1000000000000 : ℝ) (123982019709/125000000000 : ℝ) (991856157669/1000000000000 : ℝ) (123982019709/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (537/4096 : ℝ)) 7 (991856157669/1000000000000 : ℝ) (123982019709/125000000000 : ℝ) (991856157669/1000000000000 : ℝ) (123982019709/125000000000 : ℝ) (991856157669/1000000000000 : ℝ) (123982019709/125000000000 : ℝ) (991856157669/1000000000000 : ℝ) (123982019709/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (537/4096 : ℝ))) (179567731811/1000000000000 : ℝ) (89783865909/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (537/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (179567731811/1000000000000 : ℝ) (89783865909/500000000000 : ℝ) (117956773181/200000000000 : ℝ) (589783865909/1000000000000 : ℝ) (105938582387/250000000000 : ℝ) (423754329557/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (537/4096 : ℝ))) 1 (117956773181/200000000000 : ℝ) (589783865909/1000000000000 : ℝ) (105938582387/250000000000 : ℝ) (423754329557/1000000000000 : ℝ) (253384548863/500000000000 : ℝ) (506769097733/1000000000000 : ℝ) (31245216301/62500000000 : ℝ) (62490432603/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (537/4096 : ℝ))) 2 (253384548863/500000000000 : ℝ) (506769097733/1000000000000 : ℝ) (31245216301/62500000000 : ℝ) (62490432603/125000000000 : ℝ) (503346279271/1000000000000 : ℝ) (503346279279/1000000000000 : ℝ) (62916830167/125000000000 : ℝ) (100666928269/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (537/4096 : ℝ))) 3 (503346279271/1000000000000 : ℝ) (503346279279/1000000000000 : ℝ) (62916830167/125000000000 : ℝ) (100666928269/200000000000 : ℝ) (503340460303/1000000000000 : ℝ) (62917557539/125000000000 : ℝ) (503340460269/1000000000000 : ℝ) (503340460279/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (537/4096 : ℝ))) 4 (503340460303/1000000000000 : ℝ) (62917557539/125000000000 : ℝ) (503340460269/1000000000000 : ℝ) (503340460279/1000000000000 : ℝ) (251670230143/500000000000 : ℝ) (62917557537/125000000000 : ℝ) (100668092057/200000000000 : ℝ) (62917557537/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (537/4096 : ℝ))) 5 (251670230143/500000000000 : ℝ) (62917557537/125000000000 : ℝ) (100668092057/200000000000 : ℝ) (62917557537/125000000000 : ℝ) (100668092057/200000000000 : ℝ) (62917557537/125000000000 : ℝ) (100668092057/200000000000 : ℝ) (62917557537/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (537/4096 : ℝ))) 6 (100668092057/200000000000 : ℝ) (62917557537/125000000000 : ℝ) (100668092057/200000000000 : ℝ) (62917557537/125000000000 : ℝ) (100668092057/200000000000 : ℝ) (62917557537/125000000000 : ℝ) (100668092057/200000000000 : ℝ) (62917557537/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (537/4096 : ℝ))) 7 (100668092057/200000000000 : ℝ) (62917557537/125000000000 : ℝ) (100668092057/200000000000 : ℝ) (62917557537/125000000000 : ℝ) (100668092057/200000000000 : ℝ) (62917557537/125000000000 : ℝ) (100668092057/200000000000 : ℝ) (62917557537/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (537/4096 : ℝ)) hmem 8 (991856157669/1000000000000 : ℝ) (123982019709/125000000000 : ℝ) (991856157669/1000000000000 : ℝ) (123982019709/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (537/4096 : ℝ))) hcmem 8 (100668092057/200000000000 : ℝ) (62917557537/125000000000 : ℝ) (100668092057/200000000000 : ℝ) (62917557537/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (537/4096 : ℝ)) (991856157669/1000000000000 : ℝ) (123982019709/125000000000 : ℝ) (100668092057/200000000000 : ℝ) (62917557537/125000000000 : ℝ) (9964213813/12500000000 : ℝ) (797137105061/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1576_exp_lower
  have heNumeric : (2054906306789/1000000000000 : ℝ)/4 ≤ Real.exp (-5328512856113/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054906306789/1000000000000 : ℝ)/4 ≤ Real.exp ((4295/32768 : ℝ)-(797137105061/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4295/32768 : ℝ) (537/4096 : ℝ) (797137105061/1000000000000 : ℝ) (2054906306789/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1577; no trusted numerical premise.
theorem cover8_leaf1577_exp_radius : (249488282108944519/250000000000000000 : ℝ) ≤ Real.exp ((-4297/262144 : ℝ)/8) ∧ Real.exp ((-4297/262144 : ℝ)/8) ≤ (997953128435778077/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4297/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1577_exp_lower : (230028444468518239/250000000000000000 : ℝ) ≤ Real.exp ((-166515889967/250000000000 : ℝ)/8) ∧ Real.exp ((-166515889967/250000000000 : ℝ)/8) ≤ (920113777874072957/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-166515889967/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1577_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513726857781/250000000000 : ℝ) ≤ 4*Real.exp (537/4096 : ℝ)*Real.exp (-mu (radius 8 (4297/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (513726857781/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4297/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1577_exp_radius
  have hrNumeric : (2459354649/2500000000 : ℝ) ≤ Real.exp (-4297/262144 : ℝ) ∧ Real.exp (-4297/262144 : ℝ) ≤ (983741859601/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (2459354649/2500000000 : ℝ) ≤ (radius 8 (4297/32768 : ℝ)) ∧ (radius 8 (4297/32768 : ℝ)) ≤ (983741859601/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4297/32768 : ℝ)) (2459354649/2500000000 : ℝ) (983741859601/1000000000000 : ℝ) (179588289341/1000000000000 : ℝ) (44897072337/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4297/32768 : ℝ)) (2459354649/2500000000 : ℝ) (983741859601/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4297/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (2459354649/2500000000 : ℝ) (983741859601/1000000000000 : ℝ) (4959354649/5000000000 : ℝ) (991870929801/1000000000000 : ℝ) (247959404389/250000000000 : ℝ) (991837617557/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4297/32768 : ℝ)) 1 (4959354649/5000000000 : ℝ) (991870929801/1000000000000 : ℝ) (247959404389/250000000000 : ℝ) (991837617557/1000000000000 : ℝ) (495927136839/500000000000 : ℝ) (991854273679/1000000000000 : ℝ) (495927136769/500000000000 : ℝ) (49592713677/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4297/32768 : ℝ)) 2 (495927136839/500000000000 : ℝ) (991854273679/1000000000000 : ℝ) (495927136769/500000000000 : ℝ) (49592713677/50000000000 : ℝ) (123981784201/125000000000 : ℝ) (99185427361/100000000000 : ℝ) (991854273607/1000000000000 : ℝ) (99185427361/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4297/32768 : ℝ)) 3 (123981784201/125000000000 : ℝ) (99185427361/100000000000 : ℝ) (991854273607/1000000000000 : ℝ) (99185427361/100000000000 : ℝ) (991854273607/1000000000000 : ℝ) (99185427361/100000000000 : ℝ) (991854273607/1000000000000 : ℝ) (99185427361/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4297/32768 : ℝ)) 4 (991854273607/1000000000000 : ℝ) (99185427361/100000000000 : ℝ) (991854273607/1000000000000 : ℝ) (99185427361/100000000000 : ℝ) (991854273607/1000000000000 : ℝ) (99185427361/100000000000 : ℝ) (991854273607/1000000000000 : ℝ) (99185427361/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4297/32768 : ℝ)) 5 (991854273607/1000000000000 : ℝ) (99185427361/100000000000 : ℝ) (991854273607/1000000000000 : ℝ) (99185427361/100000000000 : ℝ) (991854273607/1000000000000 : ℝ) (99185427361/100000000000 : ℝ) (991854273607/1000000000000 : ℝ) (99185427361/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4297/32768 : ℝ)) 6 (991854273607/1000000000000 : ℝ) (99185427361/100000000000 : ℝ) (991854273607/1000000000000 : ℝ) (99185427361/100000000000 : ℝ) (991854273607/1000000000000 : ℝ) (99185427361/100000000000 : ℝ) (991854273607/1000000000000 : ℝ) (99185427361/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4297/32768 : ℝ)) 7 (991854273607/1000000000000 : ℝ) (99185427361/100000000000 : ℝ) (991854273607/1000000000000 : ℝ) (99185427361/100000000000 : ℝ) (991854273607/1000000000000 : ℝ) (99185427361/100000000000 : ℝ) (991854273607/1000000000000 : ℝ) (99185427361/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4297/32768 : ℝ))) (179588289341/1000000000000 : ℝ) (44897072337/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4297/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (179588289341/1000000000000 : ℝ) (44897072337/250000000000 : ℝ) (58979414467/100000000000 : ℝ) (294897072337/500000000000 : ℝ) (211889292639/500000000000 : ℝ) (52972323161/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4297/32768 : ℝ))) 1 (58979414467/100000000000 : ℝ) (294897072337/500000000000 : ℝ) (211889292639/500000000000 : ℝ) (52972323161/125000000000 : ℝ) (253393182487/500000000000 : ℝ) (506786364981/1000000000000 : ℝ) (499942124883/1000000000000 : ℝ) (124985531223/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4297/32768 : ℝ))) 2 (253393182487/500000000000 : ℝ) (506786364981/1000000000000 : ℝ) (499942124883/1000000000000 : ℝ) (124985531223/250000000000 : ℝ) (7865066327/15625000000 : ℝ) (503364244937/1000000000000 : ℝ) (251676306079/500000000000 : ℝ) (503352612167/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4297/32768 : ℝ))) 3 (7865066327/15625000000 : ℝ) (503364244937/1000000000000 : ℝ) (251676306079/500000000000 : ℝ) (503352612167/1000000000000 : ℝ) (503358428543/1000000000000 : ℝ) (62919803569/125000000000 : ℝ) (503358428509/1000000000000 : ℝ) (503358428519/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4297/32768 : ℝ))) 4 (503358428543/1000000000000 : ℝ) (62919803569/125000000000 : ℝ) (503358428509/1000000000000 : ℝ) (503358428519/1000000000000 : ℝ) (251679214263/500000000000 : ℝ) (62919803567/125000000000 : ℝ) (20134337141/40000000000 : ℝ) (62919803567/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4297/32768 : ℝ))) 5 (251679214263/500000000000 : ℝ) (62919803567/125000000000 : ℝ) (20134337141/40000000000 : ℝ) (62919803567/125000000000 : ℝ) (20134337141/40000000000 : ℝ) (62919803567/125000000000 : ℝ) (20134337141/40000000000 : ℝ) (62919803567/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4297/32768 : ℝ))) 6 (20134337141/40000000000 : ℝ) (62919803567/125000000000 : ℝ) (20134337141/40000000000 : ℝ) (62919803567/125000000000 : ℝ) (20134337141/40000000000 : ℝ) (62919803567/125000000000 : ℝ) (20134337141/40000000000 : ℝ) (62919803567/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4297/32768 : ℝ))) 7 (20134337141/40000000000 : ℝ) (62919803567/125000000000 : ℝ) (20134337141/40000000000 : ℝ) (62919803567/125000000000 : ℝ) (20134337141/40000000000 : ℝ) (62919803567/125000000000 : ℝ) (20134337141/40000000000 : ℝ) (62919803567/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4297/32768 : ℝ)) hmem 8 (991854273607/1000000000000 : ℝ) (99185427361/100000000000 : ℝ) (991854273607/1000000000000 : ℝ) (99185427361/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4297/32768 : ℝ))) hcmem 8 (20134337141/40000000000 : ℝ) (62919803567/125000000000 : ℝ) (20134337141/40000000000 : ℝ) (62919803567/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4297/32768 : ℝ)) (991854273607/1000000000000 : ℝ) (99185427361/100000000000 : ℝ) (20134337141/40000000000 : ℝ) (62919803567/125000000000 : ℝ) (49822942217/62500000000 : ℝ) (797167075493/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1577_exp_lower
  have heNumeric : (513726857781/250000000000 : ℝ)/4 ≤ Real.exp (-166515889967/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513726857781/250000000000 : ℝ)/4 ≤ Real.exp ((537/4096 : ℝ)-(797167075493/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (537/4096 : ℝ) (4297/32768 : ℝ) (797167075493/1000000000000 : ℝ) (513726857781/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1578; no trusted numerical premise.
theorem cover8_leaf1578_exp_radius : (997952652574757747/1000000000000000000 : ℝ) ≤ Real.exp ((-2149/131072 : ℝ)/8) ∧ Real.exp ((-2149/131072 : ℝ)/8) ≤ (249488163143689437/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2149/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1578_exp_lower : (920113841347333389/1000000000000000000 : ℝ) ≤ Real.exp ((-5328504063959/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328504063959/8000000000000 : ℝ)/8) ≤ (92011384134733339/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328504063959/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1578_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513727141293/250000000000 : ℝ) ≤ 4*Real.exp (4297/32768 : ℝ)*Real.exp (-mu (radius 8 (2149/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (513727141293/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2149/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1578_exp_radius
  have hrNumeric : (98373810693/100000000000 : ℝ) ≤ Real.exp (-2149/131072 : ℝ) ∧ Real.exp (-2149/131072 : ℝ) ≤ (983738106931/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98373810693/100000000000 : ℝ) ≤ (radius 8 (2149/16384 : ℝ)) ∧ (radius 8 (2149/16384 : ℝ)) ≤ (983738106931/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2149/16384 : ℝ)) (98373810693/100000000000 : ℝ) (983738106931/1000000000000 : ℝ) (89804422179/500000000000 : ℝ) (35921768873/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2149/16384 : ℝ)) (98373810693/100000000000 : ℝ) (983738106931/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2149/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98373810693/100000000000 : ℝ) (983738106931/1000000000000 : ℝ) (198373810693/200000000000 : ℝ) (495934526733/500000000000 : ℝ) (495917862889/500000000000 : ℝ) (991835725779/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2149/16384 : ℝ)) 1 (198373810693/200000000000 : ℝ) (495934526733/500000000000 : ℝ) (495917862889/500000000000 : ℝ) (991835725779/1000000000000 : ℝ) (991852389621/1000000000000 : ℝ) (991852389623/1000000000000 : ℝ) (991852389481/1000000000000 : ℝ) (991852389483/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2149/16384 : ℝ)) 2 (991852389621/1000000000000 : ℝ) (991852389623/1000000000000 : ℝ) (991852389481/1000000000000 : ℝ) (991852389483/1000000000000 : ℝ) (991852389551/1000000000000 : ℝ) (991852389553/1000000000000 : ℝ) (19837047791/20000000000 : ℝ) (991852389553/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2149/16384 : ℝ)) 3 (991852389551/1000000000000 : ℝ) (991852389553/1000000000000 : ℝ) (19837047791/20000000000 : ℝ) (991852389553/1000000000000 : ℝ) (19837047791/20000000000 : ℝ) (991852389553/1000000000000 : ℝ) (19837047791/20000000000 : ℝ) (991852389553/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2149/16384 : ℝ)) 4 (19837047791/20000000000 : ℝ) (991852389553/1000000000000 : ℝ) (19837047791/20000000000 : ℝ) (991852389553/1000000000000 : ℝ) (19837047791/20000000000 : ℝ) (991852389553/1000000000000 : ℝ) (19837047791/20000000000 : ℝ) (991852389553/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2149/16384 : ℝ)) 5 (19837047791/20000000000 : ℝ) (991852389553/1000000000000 : ℝ) (19837047791/20000000000 : ℝ) (991852389553/1000000000000 : ℝ) (19837047791/20000000000 : ℝ) (991852389553/1000000000000 : ℝ) (19837047791/20000000000 : ℝ) (991852389553/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2149/16384 : ℝ)) 6 (19837047791/20000000000 : ℝ) (991852389553/1000000000000 : ℝ) (19837047791/20000000000 : ℝ) (991852389553/1000000000000 : ℝ) (19837047791/20000000000 : ℝ) (991852389553/1000000000000 : ℝ) (19837047791/20000000000 : ℝ) (991852389553/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2149/16384 : ℝ)) 7 (19837047791/20000000000 : ℝ) (991852389553/1000000000000 : ℝ) (19837047791/20000000000 : ℝ) (991852389553/1000000000000 : ℝ) (19837047791/20000000000 : ℝ) (991852389553/1000000000000 : ℝ) (19837047791/20000000000 : ℝ) (991852389553/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2149/16384 : ℝ))) (89804422179/500000000000 : ℝ) (35921768873/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2149/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89804422179/500000000000 : ℝ) (35921768873/200000000000 : ℝ) (589804422179/1000000000000 : ℝ) (589804422183/1000000000000 : ℝ) (26487677291/62500000000 : ℝ) (84760567333/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2149/16384 : ℝ))) 1 (589804422179/1000000000000 : ℝ) (589804422183/1000000000000 : ℝ) (26487677291/62500000000 : ℝ) (84760567333/200000000000 : ℝ) (506803629417/1000000000000 : ℝ) (31675226839/62500000000 : ℝ) (499960785653/1000000000000 : ℝ) (499960785661/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2149/16384 : ℝ))) 2 (506803629417/1000000000000 : ℝ) (31675226839/62500000000 : ℝ) (499960785653/1000000000000 : ℝ) (499960785661/1000000000000 : ℝ) (100676441507/200000000000 : ℝ) (503382207543/1000000000000 : ℝ) (251685289963/500000000000 : ℝ) (251685289967/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2149/16384 : ℝ))) 3 (100676441507/200000000000 : ℝ) (503382207543/1000000000000 : ℝ) (251685289963/500000000000 : ℝ) (251685289967/500000000000 : ℝ) (50337639373/100000000000 : ℝ) (503376393739/1000000000000 : ℝ) (15730512303/31250000000 : ℝ) (100675278741/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2149/16384 : ℝ))) 4 (50337639373/100000000000 : ℝ) (503376393739/1000000000000 : ℝ) (15730512303/31250000000 : ℝ) (100675278741/200000000000 : ℝ) (503376393713/1000000000000 : ℝ) (251688196861/500000000000 : ℝ) (31461024607/62500000000 : ℝ) (251688196861/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2149/16384 : ℝ))) 5 (503376393713/1000000000000 : ℝ) (251688196861/500000000000 : ℝ) (31461024607/62500000000 : ℝ) (251688196861/500000000000 : ℝ) (31461024607/62500000000 : ℝ) (251688196861/500000000000 : ℝ) (31461024607/62500000000 : ℝ) (251688196861/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2149/16384 : ℝ))) 6 (31461024607/62500000000 : ℝ) (251688196861/500000000000 : ℝ) (31461024607/62500000000 : ℝ) (251688196861/500000000000 : ℝ) (31461024607/62500000000 : ℝ) (251688196861/500000000000 : ℝ) (31461024607/62500000000 : ℝ) (251688196861/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2149/16384 : ℝ))) 7 (31461024607/62500000000 : ℝ) (251688196861/500000000000 : ℝ) (31461024607/62500000000 : ℝ) (251688196861/500000000000 : ℝ) (31461024607/62500000000 : ℝ) (251688196861/500000000000 : ℝ) (31461024607/62500000000 : ℝ) (251688196861/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2149/16384 : ℝ)) hmem 8 (19837047791/20000000000 : ℝ) (991852389553/1000000000000 : ℝ) (19837047791/20000000000 : ℝ) (991852389553/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2149/16384 : ℝ))) hcmem 8 (31461024607/62500000000 : ℝ) (251688196861/500000000000 : ℝ) (31461024607/62500000000 : ℝ) (251688196861/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2149/16384 : ℝ)) (19837047791/20000000000 : ℝ) (991852389553/1000000000000 : ℝ) (31461024607/62500000000 : ℝ) (251688196861/500000000000 : ℝ) (797197041179/1000000000000 : ℝ) (398598520599/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1578_exp_lower
  have heNumeric : (513727141293/250000000000 : ℝ)/4 ≤ Real.exp (-5328504063959/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513727141293/250000000000 : ℝ)/4 ≤ Real.exp ((4297/32768 : ℝ)-(398598520599/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4297/32768 : ℝ) (2149/16384 : ℝ) (398598520599/500000000000 : ℝ) (513727141293/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1579; no trusted numerical premise.
theorem cover8_leaf1579_exp_radius : (498976088356982163/500000000000000000 : ℝ) ≤ Real.exp ((-4299/262144 : ℝ)/8) ∧ Real.exp ((-4299/262144 : ℝ)/8) ≤ (997952176713964327/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4299/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1579_exp_lower : (230028476340751337/250000000000000000 : ℝ) ≤ Real.exp ((-2664249805623/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664249805623/4000000000000 : ℝ)/8) ≤ (920113905363005349/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664249805623/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1579_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431856807/62500000000 : ℝ) ≤ 4*Real.exp (2149/16384 : ℝ)*Real.exp (-mu (radius 8 (4299/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (128431856807/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4299/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1579_exp_radius
  have hrNumeric : (491867177137/500000000000 : ℝ) ≤ Real.exp (-4299/262144 : ℝ) ∧ Real.exp (-4299/262144 : ℝ) ≤ (39349374171/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491867177137/500000000000 : ℝ) ≤ (radius 8 (4299/32768 : ℝ)) ∧ (radius 8 (4299/32768 : ℝ)) ≤ (39349374171/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4299/32768 : ℝ)) (491867177137/500000000000 : ℝ) (39349374171/40000000000 : ℝ) (179629396867/1000000000000 : ℝ) (89814698437/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4299/32768 : ℝ)) (491867177137/500000000000 : ℝ) (39349374171/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4299/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491867177137/500000000000 : ℝ) (39349374171/40000000000 : ℝ) (991867177137/1000000000000 : ℝ) (495933588569/500000000000 : ℝ) (991833834003/1000000000000 : ℝ) (247958458501/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4299/32768 : ℝ)) 1 (991867177137/1000000000000 : ℝ) (495933588569/500000000000 : ℝ) (991833834003/1000000000000 : ℝ) (247958458501/250000000000 : ℝ) (99185050557/100000000000 : ℝ) (991850505571/1000000000000 : ℝ) (991850505429/1000000000000 : ℝ) (991850505431/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4299/32768 : ℝ)) 2 (99185050557/100000000000 : ℝ) (991850505571/1000000000000 : ℝ) (991850505429/1000000000000 : ℝ) (991850505431/1000000000000 : ℝ) (991850505499/1000000000000 : ℝ) (991850505501/1000000000000 : ℝ) (991850505499/1000000000000 : ℝ) (991850505501/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4299/32768 : ℝ)) 3 (991850505499/1000000000000 : ℝ) (991850505501/1000000000000 : ℝ) (991850505499/1000000000000 : ℝ) (991850505501/1000000000000 : ℝ) (991850505499/1000000000000 : ℝ) (991850505501/1000000000000 : ℝ) (991850505499/1000000000000 : ℝ) (991850505501/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4299/32768 : ℝ)) 4 (991850505499/1000000000000 : ℝ) (991850505501/1000000000000 : ℝ) (991850505499/1000000000000 : ℝ) (991850505501/1000000000000 : ℝ) (991850505499/1000000000000 : ℝ) (991850505501/1000000000000 : ℝ) (991850505499/1000000000000 : ℝ) (991850505501/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4299/32768 : ℝ)) 5 (991850505499/1000000000000 : ℝ) (991850505501/1000000000000 : ℝ) (991850505499/1000000000000 : ℝ) (991850505501/1000000000000 : ℝ) (991850505499/1000000000000 : ℝ) (991850505501/1000000000000 : ℝ) (991850505499/1000000000000 : ℝ) (991850505501/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4299/32768 : ℝ)) 6 (991850505499/1000000000000 : ℝ) (991850505501/1000000000000 : ℝ) (991850505499/1000000000000 : ℝ) (991850505501/1000000000000 : ℝ) (991850505499/1000000000000 : ℝ) (991850505501/1000000000000 : ℝ) (991850505499/1000000000000 : ℝ) (991850505501/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4299/32768 : ℝ)) 7 (991850505499/1000000000000 : ℝ) (991850505501/1000000000000 : ℝ) (991850505499/1000000000000 : ℝ) (991850505501/1000000000000 : ℝ) (991850505499/1000000000000 : ℝ) (991850505501/1000000000000 : ℝ) (991850505499/1000000000000 : ℝ) (991850505501/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4299/32768 : ℝ))) (179629396867/1000000000000 : ℝ) (89814698437/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4299/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (179629396867/1000000000000 : ℝ) (89814698437/500000000000 : ℝ) (589814698433/1000000000000 : ℝ) (589814698437/1000000000000 : ℝ) (423827083687/1000000000000 : ℝ) (26489192731/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4299/32768 : ℝ))) 1 (589814698433/1000000000000 : ℝ) (589814698437/1000000000000 : ℝ) (423827083687/1000000000000 : ℝ) (26489192731/62500000000 : ℝ) (25341044553/50000000000 : ℝ) (506820891067/1000000000000 : ℝ) (49997944313/100000000000 : ℝ) (249989721569/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4299/32768 : ℝ))) 2 (25341044553/50000000000 : ℝ) (506820891067/1000000000000 : ℝ) (49997944313/100000000000 : ℝ) (249989721569/500000000000 : ℝ) (100680033419/200000000000 : ℝ) (503400167103/1000000000000 : ℝ) (125847136161/250000000000 : ℝ) (125847136163/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4299/32768 : ℝ))) 3 (100680033419/200000000000 : ℝ) (503400167103/1000000000000 : ℝ) (125847136161/250000000000 : ℝ) (125847136163/250000000000 : ℝ) (503394355869/1000000000000 : ℝ) (251697177939/500000000000 : ℝ) (100678871167/200000000000 : ℝ) (125848588961/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4299/32768 : ℝ))) 4 (503394355869/1000000000000 : ℝ) (251697177939/500000000000 : ℝ) (100678871167/200000000000 : ℝ) (125848588961/250000000000 : ℝ) (125848588963/250000000000 : ℝ) (503394355861/1000000000000 : ℝ) (503394355851/1000000000000 : ℝ) (503394355861/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4299/32768 : ℝ))) 5 (125848588963/250000000000 : ℝ) (503394355861/1000000000000 : ℝ) (503394355851/1000000000000 : ℝ) (503394355861/1000000000000 : ℝ) (503394355851/1000000000000 : ℝ) (503394355861/1000000000000 : ℝ) (503394355851/1000000000000 : ℝ) (503394355861/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4299/32768 : ℝ))) 6 (503394355851/1000000000000 : ℝ) (503394355861/1000000000000 : ℝ) (503394355851/1000000000000 : ℝ) (503394355861/1000000000000 : ℝ) (503394355851/1000000000000 : ℝ) (503394355861/1000000000000 : ℝ) (503394355851/1000000000000 : ℝ) (503394355861/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4299/32768 : ℝ))) 7 (503394355851/1000000000000 : ℝ) (503394355861/1000000000000 : ℝ) (503394355851/1000000000000 : ℝ) (503394355861/1000000000000 : ℝ) (503394355851/1000000000000 : ℝ) (503394355861/1000000000000 : ℝ) (503394355851/1000000000000 : ℝ) (503394355861/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4299/32768 : ℝ)) hmem 8 (991850505499/1000000000000 : ℝ) (991850505501/1000000000000 : ℝ) (991850505499/1000000000000 : ℝ) (991850505501/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4299/32768 : ℝ))) hcmem 8 (503394355851/1000000000000 : ℝ) (503394355861/1000000000000 : ℝ) (503394355851/1000000000000 : ℝ) (503394355861/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4299/32768 : ℝ)) (991850505499/1000000000000 : ℝ) (991850505501/1000000000000 : ℝ) (503394355851/1000000000000 : ℝ) (503394355861/1000000000000 : ℝ) (99653375271/125000000000 : ℝ) (797227002187/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1579_exp_lower
  have heNumeric : (128431856807/62500000000 : ℝ)/4 ≤ Real.exp (-2664249805623/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431856807/62500000000 : ℝ)/4 ≤ Real.exp ((2149/16384 : ℝ)-(797227002187/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2149/16384 : ℝ) (4299/32768 : ℝ) (797227002187/1000000000000 : ℝ) (128431856807/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1580; no trusted numerical premise.
theorem cover8_leaf1580_exp_radius : (997951700853397813/1000000000000000000 : ℝ) ≤ Real.exp ((-1075/65536 : ℝ)/8) ∧ Real.exp ((-1075/65536 : ℝ)/8) ≤ (498975850426698907/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1075/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1580_exp_lower : (460056984960947023/500000000000000000 : ℝ) ≤ Real.exp ((-5328495120749/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328495120749/8000000000000 : ℝ)/8) ≤ (920113969921894047/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328495120749/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1580_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027455431179/500000000000 : ℝ) ≤ 4*Real.exp (4299/32768 : ℝ)*Real.exp (-mu (radius 8 (1075/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (1027455431179/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1075/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1580_exp_radius
  have hrNumeric : (983730601633/1000000000000 : ℝ) ≤ Real.exp (-1075/65536 : ℝ) ∧ Real.exp (-1075/65536 : ℝ) ≤ (491865300817/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983730601633/1000000000000 : ℝ) ≤ (radius 8 (1075/8192 : ℝ)) ∧ (radius 8 (1075/8192 : ℝ)) ≤ (491865300817/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1075/8192 : ℝ)) (983730601633/1000000000000 : ℝ) (491865300817/500000000000 : ℝ) (35929989373/200000000000 : ℝ) (22456243359/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1075/8192 : ℝ)) (983730601633/1000000000000 : ℝ) (491865300817/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1075/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983730601633/1000000000000 : ℝ) (491865300817/500000000000 : ℝ) (61991581301/62500000000 : ℝ) (991865300817/1000000000000 : ℝ) (123978992779/125000000000 : ℝ) (495915971117/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1075/8192 : ℝ)) 1 (61991581301/62500000000 : ℝ) (991865300817/1000000000000 : ℝ) (123978992779/125000000000 : ℝ) (495915971117/500000000000 : ℝ) (247962155381/250000000000 : ℝ) (495924310763/500000000000 : ℝ) (991848621383/1000000000000 : ℝ) (495924310693/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1075/8192 : ℝ)) 2 (247962155381/250000000000 : ℝ) (495924310763/500000000000 : ℝ) (991848621383/1000000000000 : ℝ) (495924310693/500000000000 : ℝ) (991848621453/1000000000000 : ℝ) (61990538841/62500000000 : ℝ) (991848621453/1000000000000 : ℝ) (61990538841/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1075/8192 : ℝ)) 3 (991848621453/1000000000000 : ℝ) (61990538841/62500000000 : ℝ) (991848621453/1000000000000 : ℝ) (61990538841/62500000000 : ℝ) (991848621453/1000000000000 : ℝ) (61990538841/62500000000 : ℝ) (991848621453/1000000000000 : ℝ) (61990538841/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1075/8192 : ℝ)) 4 (991848621453/1000000000000 : ℝ) (61990538841/62500000000 : ℝ) (991848621453/1000000000000 : ℝ) (61990538841/62500000000 : ℝ) (991848621453/1000000000000 : ℝ) (61990538841/62500000000 : ℝ) (991848621453/1000000000000 : ℝ) (61990538841/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1075/8192 : ℝ)) 5 (991848621453/1000000000000 : ℝ) (61990538841/62500000000 : ℝ) (991848621453/1000000000000 : ℝ) (61990538841/62500000000 : ℝ) (991848621453/1000000000000 : ℝ) (61990538841/62500000000 : ℝ) (991848621453/1000000000000 : ℝ) (61990538841/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1075/8192 : ℝ)) 6 (991848621453/1000000000000 : ℝ) (61990538841/62500000000 : ℝ) (991848621453/1000000000000 : ℝ) (61990538841/62500000000 : ℝ) (991848621453/1000000000000 : ℝ) (61990538841/62500000000 : ℝ) (991848621453/1000000000000 : ℝ) (61990538841/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1075/8192 : ℝ)) 7 (991848621453/1000000000000 : ℝ) (61990538841/62500000000 : ℝ) (991848621453/1000000000000 : ℝ) (61990538841/62500000000 : ℝ) (991848621453/1000000000000 : ℝ) (61990538841/62500000000 : ℝ) (991848621453/1000000000000 : ℝ) (61990538841/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1075/8192 : ℝ))) (35929989373/200000000000 : ℝ) (22456243359/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1075/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35929989373/200000000000 : ℝ) (22456243359/125000000000 : ℝ) (73728121679/125000000000 : ℝ) (147456243359/250000000000 : ℝ) (423851326369/1000000000000 : ℝ) (211925663189/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1075/8192 : ℝ))) 1 (73728121679/125000000000 : ℝ) (147456243359/250000000000 : ℝ) (423851326369/1000000000000 : ℝ) (211925663189/500000000000 : ℝ) (5068381499/10000000000 : ℝ) (506838149907/1000000000000 : ℝ) (499998097311/1000000000000 : ℝ) (499998097319/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1075/8192 : ℝ))) 2 (5068381499/10000000000 : ℝ) (506838149907/1000000000000 : ℝ) (499998097311/1000000000000 : ℝ) (499998097319/1000000000000 : ℝ) (100683624721/200000000000 : ℝ) (503418123613/1000000000000 : ℝ) (503406506309/1000000000000 : ℝ) (503406506317/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1075/8192 : ℝ))) 3 (100683624721/200000000000 : ℝ) (503418123613/1000000000000 : ℝ) (503406506309/1000000000000 : ℝ) (503406506317/1000000000000 : ℝ) (503412314957/1000000000000 : ℝ) (100682462993/200000000000 : ℝ) (503412314923/1000000000000 : ℝ) (125853078733/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1075/8192 : ℝ))) 4 (503412314957/1000000000000 : ℝ) (100682462993/200000000000 : ℝ) (503412314923/1000000000000 : ℝ) (125853078733/250000000000 : ℝ) (25170615747/50000000000 : ℝ) (503412314949/1000000000000 : ℝ) (503412314939/1000000000000 : ℝ) (503412314949/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1075/8192 : ℝ))) 5 (25170615747/50000000000 : ℝ) (503412314949/1000000000000 : ℝ) (503412314939/1000000000000 : ℝ) (503412314949/1000000000000 : ℝ) (503412314939/1000000000000 : ℝ) (503412314949/1000000000000 : ℝ) (503412314939/1000000000000 : ℝ) (503412314949/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1075/8192 : ℝ))) 6 (503412314939/1000000000000 : ℝ) (503412314949/1000000000000 : ℝ) (503412314939/1000000000000 : ℝ) (503412314949/1000000000000 : ℝ) (503412314939/1000000000000 : ℝ) (503412314949/1000000000000 : ℝ) (503412314939/1000000000000 : ℝ) (503412314949/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1075/8192 : ℝ))) 7 (503412314939/1000000000000 : ℝ) (503412314949/1000000000000 : ℝ) (503412314939/1000000000000 : ℝ) (503412314949/1000000000000 : ℝ) (503412314939/1000000000000 : ℝ) (503412314949/1000000000000 : ℝ) (503412314939/1000000000000 : ℝ) (503412314949/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1075/8192 : ℝ)) hmem 8 (991848621453/1000000000000 : ℝ) (61990538841/62500000000 : ℝ) (991848621453/1000000000000 : ℝ) (61990538841/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1075/8192 : ℝ))) hcmem 8 (503412314939/1000000000000 : ℝ) (503412314949/1000000000000 : ℝ) (503412314939/1000000000000 : ℝ) (503412314949/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1075/8192 : ℝ)) (991848621453/1000000000000 : ℝ) (61990538841/62500000000 : ℝ) (503412314939/1000000000000 : ℝ) (503412314949/1000000000000 : ℝ) (398628479217/500000000000 : ℝ) (797256958453/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1580_exp_lower
  have heNumeric : (1027455431179/500000000000 : ℝ)/4 ≤ Real.exp (-5328495120749/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027455431179/500000000000 : ℝ)/4 ≤ Real.exp ((4299/32768 : ℝ)-(797256958453/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4299/32768 : ℝ) (1075/8192 : ℝ) (797256958453/1000000000000 : ℝ) (1027455431179/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1581; no trusted numerical premise.
theorem cover8_leaf1581_exp_radius : (31185975781033069/31250000000000000 : ℝ) ≤ Real.exp ((-4301/262144 : ℝ)/8) ∧ Real.exp ((-4301/262144 : ℝ)/8) ≤ (997951224993058209/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4301/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1581_exp_lower : (46005701751096467/50000000000000000 : ℝ) ≤ Real.exp ((-1332122648153/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332122648153/2000000000000 : ℝ)/8) ≤ (920114035021929341/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332122648153/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1581_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054912025473/1000000000000 : ℝ) ≤ 4*Real.exp (1075/8192 : ℝ)*Real.exp (-mu (radius 8 (4301/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054912025473/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4301/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1581_exp_radius
  have hrNumeric : (196745369801/200000000000 : ℝ) ≤ Real.exp (-4301/262144 : ℝ) ∧ Real.exp (-4301/262144 : ℝ) ≤ (491863424503/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196745369801/200000000000 : ℝ) ≤ (radius 8 (4301/32768 : ℝ)) ∧ (radius 8 (4301/32768 : ℝ)) ≤ (491863424503/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4301/32768 : ℝ)) (196745369801/200000000000 : ℝ) (491863424503/500000000000 : ℝ) (179670494363/1000000000000 : ℝ) (179670494369/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4301/32768 : ℝ)) (196745369801/200000000000 : ℝ) (491863424503/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4301/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196745369801/200000000000 : ℝ) (491863424503/500000000000 : ℝ) (495931712251/500000000000 : ℝ) (991863424503/1000000000000 : ℝ) (30994689077/31250000000 : ℝ) (495915025233/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4301/32768 : ℝ)) 1 (495931712251/500000000000 : ℝ) (991863424503/1000000000000 : ℝ) (30994689077/31250000000 : ℝ) (495915025233/500000000000 : ℝ) (991846737483/1000000000000 : ℝ) (198369347497/200000000000 : ℝ) (495923368671/500000000000 : ℝ) (198369347469/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4301/32768 : ℝ)) 2 (991846737483/1000000000000 : ℝ) (198369347497/200000000000 : ℝ) (495923368671/500000000000 : ℝ) (198369347469/200000000000 : ℝ) (247961684353/250000000000 : ℝ) (198369347483/200000000000 : ℝ) (247961684353/250000000000 : ℝ) (198369347483/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4301/32768 : ℝ)) 3 (247961684353/250000000000 : ℝ) (198369347483/200000000000 : ℝ) (247961684353/250000000000 : ℝ) (198369347483/200000000000 : ℝ) (247961684353/250000000000 : ℝ) (198369347483/200000000000 : ℝ) (247961684353/250000000000 : ℝ) (198369347483/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4301/32768 : ℝ)) 4 (247961684353/250000000000 : ℝ) (198369347483/200000000000 : ℝ) (247961684353/250000000000 : ℝ) (198369347483/200000000000 : ℝ) (247961684353/250000000000 : ℝ) (198369347483/200000000000 : ℝ) (247961684353/250000000000 : ℝ) (198369347483/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4301/32768 : ℝ)) 5 (247961684353/250000000000 : ℝ) (198369347483/200000000000 : ℝ) (247961684353/250000000000 : ℝ) (198369347483/200000000000 : ℝ) (247961684353/250000000000 : ℝ) (198369347483/200000000000 : ℝ) (247961684353/250000000000 : ℝ) (198369347483/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4301/32768 : ℝ)) 6 (247961684353/250000000000 : ℝ) (198369347483/200000000000 : ℝ) (247961684353/250000000000 : ℝ) (198369347483/200000000000 : ℝ) (247961684353/250000000000 : ℝ) (198369347483/200000000000 : ℝ) (247961684353/250000000000 : ℝ) (198369347483/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4301/32768 : ℝ)) 7 (247961684353/250000000000 : ℝ) (198369347483/200000000000 : ℝ) (247961684353/250000000000 : ℝ) (198369347483/200000000000 : ℝ) (247961684353/250000000000 : ℝ) (198369347483/200000000000 : ℝ) (247961684353/250000000000 : ℝ) (198369347483/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4301/32768 : ℝ))) (179670494363/1000000000000 : ℝ) (179670494369/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4301/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (179670494363/1000000000000 : ℝ) (179670494369/1000000000000 : ℝ) (589835247181/1000000000000 : ℝ) (117967049437/200000000000 : ℝ) (84775112943/200000000000 : ℝ) (423875564723/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4301/32768 : ℝ))) 1 (589835247181/1000000000000 : ℝ) (117967049437/200000000000 : ℝ) (84775112943/200000000000 : ℝ) (423875564723/1000000000000 : ℝ) (126713851487/250000000000 : ℝ) (253427702977/500000000000 : ℝ) (500016748207/1000000000000 : ℝ) (250008374107/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4301/32768 : ℝ))) 2 (126713851487/250000000000 : ℝ) (253427702977/500000000000 : ℝ) (500016748207/1000000000000 : ℝ) (250008374107/500000000000 : ℝ) (503436077077/1000000000000 : ℝ) (125859019271/250000000000 : ℝ) (503424464933/1000000000000 : ℝ) (25171223247/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4301/32768 : ℝ))) 3 (503436077077/1000000000000 : ℝ) (125859019271/250000000000 : ℝ) (503424464933/1000000000000 : ℝ) (25171223247/50000000000 : ℝ) (100686054201/200000000000 : ℝ) (125857567753/250000000000 : ℝ) (503430270971/1000000000000 : ℝ) (503430270979/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4301/32768 : ℝ))) 4 (100686054201/200000000000 : ℝ) (125857567753/250000000000 : ℝ) (503430270971/1000000000000 : ℝ) (503430270979/1000000000000 : ℝ) (125857567747/250000000000 : ℝ) (125857567749/250000000000 : ℝ) (503430270987/1000000000000 : ℝ) (125857567749/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4301/32768 : ℝ))) 5 (125857567747/250000000000 : ℝ) (125857567749/250000000000 : ℝ) (503430270987/1000000000000 : ℝ) (125857567749/250000000000 : ℝ) (503430270987/1000000000000 : ℝ) (125857567749/250000000000 : ℝ) (503430270987/1000000000000 : ℝ) (125857567749/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4301/32768 : ℝ))) 6 (503430270987/1000000000000 : ℝ) (125857567749/250000000000 : ℝ) (503430270987/1000000000000 : ℝ) (125857567749/250000000000 : ℝ) (503430270987/1000000000000 : ℝ) (125857567749/250000000000 : ℝ) (503430270987/1000000000000 : ℝ) (125857567749/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4301/32768 : ℝ))) 7 (503430270987/1000000000000 : ℝ) (125857567749/250000000000 : ℝ) (503430270987/1000000000000 : ℝ) (125857567749/250000000000 : ℝ) (503430270987/1000000000000 : ℝ) (125857567749/250000000000 : ℝ) (503430270987/1000000000000 : ℝ) (125857567749/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4301/32768 : ℝ)) hmem 8 (247961684353/250000000000 : ℝ) (198369347483/200000000000 : ℝ) (247961684353/250000000000 : ℝ) (198369347483/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4301/32768 : ℝ))) hcmem 8 (503430270987/1000000000000 : ℝ) (125857567749/250000000000 : ℝ) (503430270987/1000000000000 : ℝ) (125857567749/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4301/32768 : ℝ)) (247961684353/250000000000 : ℝ) (198369347483/200000000000 : ℝ) (503430270987/1000000000000 : ℝ) (125857567749/250000000000 : ℝ) (199321727499/250000000000 : ℝ) (398643455007/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1581_exp_lower
  have heNumeric : (2054912025473/1000000000000 : ℝ)/4 ≤ Real.exp (-1332122648153/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054912025473/1000000000000 : ℝ)/4 ≤ Real.exp ((1075/8192 : ℝ)-(398643455007/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1075/8192 : ℝ) (4301/32768 : ℝ) (398643455007/500000000000 : ℝ) (2054912025473/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1582; no trusted numerical premise.
theorem cover8_leaf1582_exp_radius : (997950749132945511/1000000000000000000 : ℝ) ≤ Real.exp ((-2151/131072 : ℝ)/8) ∧ Real.exp ((-2151/131072 : ℝ)/8) ≤ (124743843641618189/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2151/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1582_exp_lower : (92011410066460653/100000000000000000 : ℝ) ≤ Real.exp ((-5328486026731/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328486026731/8000000000000 : ℝ)/8) ≤ (920114100664606531/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328486026731/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1582_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513728299571/250000000000 : ℝ) ≤ 4*Real.exp (4301/32768 : ℝ)*Real.exp (-mu (radius 8 (2151/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (513728299571/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2151/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1582_exp_radius
  have hrNumeric : (122965387049/125000000000 : ℝ) ≤ Real.exp (-2151/131072 : ℝ) ∧ Real.exp (-2151/131072 : ℝ) ≤ (983723096393/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122965387049/125000000000 : ℝ) ≤ (radius 8 (2151/16384 : ℝ)) ∧ (radius 8 (2151/16384 : ℝ)) ≤ (983723096393/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2151/16384 : ℝ)) (122965387049/125000000000 : ℝ) (983723096393/1000000000000 : ℝ) (3593820787/20000000000 : ℝ) (179691039357/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2151/16384 : ℝ)) (122965387049/125000000000 : ℝ) (983723096393/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2151/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122965387049/125000000000 : ℝ) (983723096393/1000000000000 : ℝ) (247965387049/250000000000 : ℝ) (991861548197/1000000000000 : ℝ) (9918281587/10000000000 : ℝ) (495914079351/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2151/16384 : ℝ)) 1 (247965387049/250000000000 : ℝ) (991861548197/1000000000000 : ℝ) (9918281587/10000000000 : ℝ) (495914079351/500000000000 : ℝ) (123980606681/125000000000 : ℝ) (19836897069/20000000000 : ℝ) (991844853307/1000000000000 : ℝ) (991844853309/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2151/16384 : ℝ)) 2 (123980606681/125000000000 : ℝ) (19836897069/20000000000 : ℝ) (991844853307/1000000000000 : ℝ) (991844853309/1000000000000 : ℝ) (991844853377/1000000000000 : ℝ) (49592242669/50000000000 : ℝ) (991844853377/1000000000000 : ℝ) (49592242669/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2151/16384 : ℝ)) 3 (991844853377/1000000000000 : ℝ) (49592242669/50000000000 : ℝ) (991844853377/1000000000000 : ℝ) (49592242669/50000000000 : ℝ) (991844853377/1000000000000 : ℝ) (49592242669/50000000000 : ℝ) (991844853377/1000000000000 : ℝ) (49592242669/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2151/16384 : ℝ)) 4 (991844853377/1000000000000 : ℝ) (49592242669/50000000000 : ℝ) (991844853377/1000000000000 : ℝ) (49592242669/50000000000 : ℝ) (991844853377/1000000000000 : ℝ) (49592242669/50000000000 : ℝ) (991844853377/1000000000000 : ℝ) (49592242669/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2151/16384 : ℝ)) 5 (991844853377/1000000000000 : ℝ) (49592242669/50000000000 : ℝ) (991844853377/1000000000000 : ℝ) (49592242669/50000000000 : ℝ) (991844853377/1000000000000 : ℝ) (49592242669/50000000000 : ℝ) (991844853377/1000000000000 : ℝ) (49592242669/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2151/16384 : ℝ)) 6 (991844853377/1000000000000 : ℝ) (49592242669/50000000000 : ℝ) (991844853377/1000000000000 : ℝ) (49592242669/50000000000 : ℝ) (991844853377/1000000000000 : ℝ) (49592242669/50000000000 : ℝ) (991844853377/1000000000000 : ℝ) (49592242669/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2151/16384 : ℝ)) 7 (991844853377/1000000000000 : ℝ) (49592242669/50000000000 : ℝ) (991844853377/1000000000000 : ℝ) (49592242669/50000000000 : ℝ) (991844853377/1000000000000 : ℝ) (49592242669/50000000000 : ℝ) (991844853377/1000000000000 : ℝ) (49592242669/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2151/16384 : ℝ))) (3593820787/20000000000 : ℝ) (179691039357/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2151/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (3593820787/20000000000 : ℝ) (179691039357/1000000000000 : ℝ) (23593820787/40000000000 : ℝ) (589845519679/1000000000000 : ℝ) (211949899357/500000000000 : ℝ) (423899798723/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2151/16384 : ℝ))) 1 (23593820787/40000000000 : ℝ) (589845519679/1000000000000 : ℝ) (211949899357/500000000000 : ℝ) (423899798723/1000000000000 : ℝ) (253436329597/500000000000 : ℝ) (506872659201/1000000000000 : ℝ) (500035395809/1000000000000 : ℝ) (500035395817/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2151/16384 : ℝ))) 2 (253436329597/500000000000 : ℝ) (506872659201/1000000000000 : ℝ) (500035395809/1000000000000 : ℝ) (500035395817/1000000000000 : ℝ) (503454027501/1000000000000 : ℝ) (503454027509/1000000000000 : ℝ) (100688484101/200000000000 : ℝ) (251721210257/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2151/16384 : ℝ))) 3 (503454027501/1000000000000 : ℝ) (503454027509/1000000000000 : ℝ) (100688484101/200000000000 : ℝ) (251721210257/500000000000 : ℝ) (503448224003/1000000000000 : ℝ) (125862056003/250000000000 : ℝ) (503448223969/1000000000000 : ℝ) (503448223979/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2151/16384 : ℝ))) 4 (503448224003/1000000000000 : ℝ) (125862056003/250000000000 : ℝ) (503448223969/1000000000000 : ℝ) (503448223979/1000000000000 : ℝ) (251724111993/500000000000 : ℝ) (125862055999/250000000000 : ℝ) (100689644797/200000000000 : ℝ) (125862055999/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2151/16384 : ℝ))) 5 (251724111993/500000000000 : ℝ) (125862055999/250000000000 : ℝ) (100689644797/200000000000 : ℝ) (125862055999/250000000000 : ℝ) (100689644797/200000000000 : ℝ) (125862055999/250000000000 : ℝ) (100689644797/200000000000 : ℝ) (125862055999/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2151/16384 : ℝ))) 6 (100689644797/200000000000 : ℝ) (125862055999/250000000000 : ℝ) (100689644797/200000000000 : ℝ) (125862055999/250000000000 : ℝ) (100689644797/200000000000 : ℝ) (125862055999/250000000000 : ℝ) (100689644797/200000000000 : ℝ) (125862055999/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2151/16384 : ℝ))) 7 (100689644797/200000000000 : ℝ) (125862055999/250000000000 : ℝ) (100689644797/200000000000 : ℝ) (125862055999/250000000000 : ℝ) (100689644797/200000000000 : ℝ) (125862055999/250000000000 : ℝ) (100689644797/200000000000 : ℝ) (125862055999/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2151/16384 : ℝ)) hmem 8 (991844853377/1000000000000 : ℝ) (49592242669/50000000000 : ℝ) (991844853377/1000000000000 : ℝ) (49592242669/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2151/16384 : ℝ))) hcmem 8 (100689644797/200000000000 : ℝ) (125862055999/250000000000 : ℝ) (100689644797/200000000000 : ℝ) (125862055999/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2151/16384 : ℝ)) (991844853377/1000000000000 : ℝ) (49592242669/50000000000 : ℝ) (100689644797/200000000000 : ℝ) (125862055999/250000000000 : ℝ) (797316856837/1000000000000 : ℝ) (797316856857/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1582_exp_lower
  have heNumeric : (513728299571/250000000000 : ℝ)/4 ≤ Real.exp (-5328486026731/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513728299571/250000000000 : ℝ)/4 ≤ Real.exp ((4301/32768 : ℝ)-(797316856857/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4301/32768 : ℝ) (2151/16384 : ℝ) (797316856857/1000000000000 : ℝ) (513728299571/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1583; no trusted numerical premise.
theorem cover8_leaf1583_exp_radius : (498975136636529861/500000000000000000 : ℝ) ≤ Real.exp ((-4303/262144 : ℝ)/8) ∧ Real.exp ((-4303/262144 : ℝ)/8) ≤ (997950273273059723/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4303/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1583_exp_lower : (184022833369939141/200000000000000000 : ℝ) ≤ Real.exp ((-2664240711561/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664240711561/4000000000000 : ℝ)/8) ≤ (460057083424847853/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664240711561/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1583_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054914380787/1000000000000 : ℝ) ≤ 4*Real.exp (2151/16384 : ℝ)*Real.exp (-mu (radius 8 (4303/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054914380787/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4303/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1583_exp_radius
  have hrNumeric : (491859671897/500000000000 : ℝ) ≤ Real.exp (-4303/262144 : ℝ) ∧ Real.exp (-4303/262144 : ℝ) ≤ (196743868759/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491859671897/500000000000 : ℝ) ≤ (radius 8 (4303/32768 : ℝ)) ∧ (radius 8 (4303/32768 : ℝ)) ≤ (196743868759/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4303/32768 : ℝ)) (491859671897/500000000000 : ℝ) (196743868759/200000000000 : ℝ) (179711581829/1000000000000 : ℝ) (35942316367/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4303/32768 : ℝ)) (491859671897/500000000000 : ℝ) (196743868759/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4303/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491859671897/500000000000 : ℝ) (196743868759/200000000000 : ℝ) (991859671897/1000000000000 : ℝ) (495929835949/500000000000 : ℝ) (49591313347/50000000000 : ℝ) (495913133471/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4303/32768 : ℝ)) 1 (991859671897/1000000000000 : ℝ) (495929835949/500000000000 : ℝ) (49591313347/50000000000 : ℝ) (495913133471/500000000000 : ℝ) (495921484709/500000000000 : ℝ) (49592148471/50000000000 : ℝ) (991842969277/1000000000000 : ℝ) (3099509279/3125000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4303/32768 : ℝ)) 2 (495921484709/500000000000 : ℝ) (49592148471/50000000000 : ℝ) (991842969277/1000000000000 : ℝ) (3099509279/3125000000 : ℝ) (991842969347/1000000000000 : ℝ) (19836859387/20000000000 : ℝ) (991842969347/1000000000000 : ℝ) (19836859387/20000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4303/32768 : ℝ)) 3 (991842969347/1000000000000 : ℝ) (19836859387/20000000000 : ℝ) (991842969347/1000000000000 : ℝ) (19836859387/20000000000 : ℝ) (991842969347/1000000000000 : ℝ) (19836859387/20000000000 : ℝ) (991842969347/1000000000000 : ℝ) (19836859387/20000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4303/32768 : ℝ)) 4 (991842969347/1000000000000 : ℝ) (19836859387/20000000000 : ℝ) (991842969347/1000000000000 : ℝ) (19836859387/20000000000 : ℝ) (991842969347/1000000000000 : ℝ) (19836859387/20000000000 : ℝ) (991842969347/1000000000000 : ℝ) (19836859387/20000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4303/32768 : ℝ)) 5 (991842969347/1000000000000 : ℝ) (19836859387/20000000000 : ℝ) (991842969347/1000000000000 : ℝ) (19836859387/20000000000 : ℝ) (991842969347/1000000000000 : ℝ) (19836859387/20000000000 : ℝ) (991842969347/1000000000000 : ℝ) (19836859387/20000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4303/32768 : ℝ)) 6 (991842969347/1000000000000 : ℝ) (19836859387/20000000000 : ℝ) (991842969347/1000000000000 : ℝ) (19836859387/20000000000 : ℝ) (991842969347/1000000000000 : ℝ) (19836859387/20000000000 : ℝ) (991842969347/1000000000000 : ℝ) (19836859387/20000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4303/32768 : ℝ)) 7 (991842969347/1000000000000 : ℝ) (19836859387/20000000000 : ℝ) (991842969347/1000000000000 : ℝ) (19836859387/20000000000 : ℝ) (991842969347/1000000000000 : ℝ) (19836859387/20000000000 : ℝ) (991842969347/1000000000000 : ℝ) (19836859387/20000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4303/32768 : ℝ))) (179711581829/1000000000000 : ℝ) (35942316367/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4303/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (179711581829/1000000000000 : ℝ) (35942316367/200000000000 : ℝ) (294927895457/500000000000 : ℝ) (294927895459/500000000000 : ℝ) (423924028369/1000000000000 : ℝ) (423924028377/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4303/32768 : ℝ))) 1 (294927895457/500000000000 : ℝ) (294927895459/500000000000 : ℝ) (423924028369/1000000000000 : ℝ) (423924028377/1000000000000 : ℝ) (506889909641/1000000000000 : ℝ) (31680619353/62500000000 : ℝ) (12501351003/25000000000 : ℝ) (7813344377/15625000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4303/32768 : ℝ))) 2 (506889909641/1000000000000 : ℝ) (31680619353/62500000000 : ℝ) (12501351003/25000000000 : ℝ) (7813344377/15625000000 : ℝ) (3146699843/6250000000 : ℝ) (62933996861/125000000000 : ℝ) (50346037303/100000000000 : ℝ) (503460373039/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4303/32768 : ℝ))) 3 (3146699843/6250000000 : ℝ) (62933996861/125000000000 : ℝ) (50346037303/100000000000 : ℝ) (503460373039/1000000000000 : ℝ) (100693234791/200000000000 : ℝ) (125866543491/250000000000 : ℝ) (503466173921/1000000000000 : ℝ) (503466173931/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4303/32768 : ℝ))) 4 (100693234791/200000000000 : ℝ) (125866543491/250000000000 : ℝ) (503466173921/1000000000000 : ℝ) (503466173931/1000000000000 : ℝ) (251733086969/500000000000 : ℝ) (125866543487/250000000000 : ℝ) (503466173937/1000000000000 : ℝ) (125866543487/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4303/32768 : ℝ))) 5 (251733086969/500000000000 : ℝ) (125866543487/250000000000 : ℝ) (503466173937/1000000000000 : ℝ) (125866543487/250000000000 : ℝ) (503466173937/1000000000000 : ℝ) (125866543487/250000000000 : ℝ) (503466173937/1000000000000 : ℝ) (125866543487/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4303/32768 : ℝ))) 6 (503466173937/1000000000000 : ℝ) (125866543487/250000000000 : ℝ) (503466173937/1000000000000 : ℝ) (125866543487/250000000000 : ℝ) (503466173937/1000000000000 : ℝ) (125866543487/250000000000 : ℝ) (503466173937/1000000000000 : ℝ) (125866543487/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4303/32768 : ℝ))) 7 (503466173937/1000000000000 : ℝ) (125866543487/250000000000 : ℝ) (503466173937/1000000000000 : ℝ) (125866543487/250000000000 : ℝ) (503466173937/1000000000000 : ℝ) (125866543487/250000000000 : ℝ) (503466173937/1000000000000 : ℝ) (125866543487/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4303/32768 : ℝ)) hmem 8 (991842969347/1000000000000 : ℝ) (19836859387/20000000000 : ℝ) (991842969347/1000000000000 : ℝ) (19836859387/20000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4303/32768 : ℝ))) hcmem 8 (503466173937/1000000000000 : ℝ) (125866543487/250000000000 : ℝ) (503466173937/1000000000000 : ℝ) (125866543487/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4303/32768 : ℝ)) (991842969347/1000000000000 : ℝ) (19836859387/20000000000 : ℝ) (503466173937/1000000000000 : ℝ) (125866543487/250000000000 : ℝ) (797346798963/1000000000000 : ℝ) (99668349873/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1583_exp_lower
  have heNumeric : (2054914380787/1000000000000 : ℝ)/4 ≤ Real.exp (-2664240711561/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054914380787/1000000000000 : ℝ)/4 ≤ Real.exp ((2151/16384 : ℝ)-(99668349873/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2151/16384 : ℝ) (4303/32768 : ℝ) (99668349873/125000000000 : ℝ) (2054914380787/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1584; no trusted numerical premise.
theorem cover8_leaf1584_exp_radius : (24948744935335021/25000000000000000 : ℝ) ≤ Real.exp ((-269/16384 : ℝ)/8) ∧ Real.exp ((-269/16384 : ℝ)/8) ≤ (997949797413400841/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-269/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1584_exp_lower : (920114233575586781/1000000000000000000 : ℝ) ≤ Real.exp ((-5328476781897/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328476781897/8000000000000 : ℝ)/8) ≤ (460057116787793391/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328476781897/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1584_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256864446619/125000000000 : ℝ) ≤ 4*Real.exp (4303/32768 : ℝ)*Real.exp (-mu (radius 8 (269/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (256864446619/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (269/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1584_exp_radius
  have hrNumeric : (983715591209/1000000000000 : ℝ) ≤ Real.exp (-269/16384 : ℝ) ∧ Real.exp (-269/16384 : ℝ) ≤ (98371559121/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983715591209/1000000000000 : ℝ) ≤ (radius 8 (269/2048 : ℝ)) ∧ (radius 8 (269/2048 : ℝ)) ≤ (98371559121/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (269/2048 : ℝ)) (983715591209/1000000000000 : ℝ) (98371559121/100000000000 : ℝ) (17973212181/100000000000 : ℝ) (22466515227/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (269/2048 : ℝ)) (983715591209/1000000000000 : ℝ) (98371559121/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (269/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983715591209/1000000000000 : ℝ) (98371559121/100000000000 : ℝ) (247964448901/250000000000 : ℝ) (198371559121/200000000000 : ℝ) (991824375183/1000000000000 : ℝ) (198364875037/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (269/2048 : ℝ)) 1 (247964448901/250000000000 : ℝ) (198371559121/200000000000 : ℝ) (991824375183/1000000000000 : ℝ) (198364875037/200000000000 : ℝ) (991841085393/1000000000000 : ℝ) (198368217079/200000000000 : ℝ) (247960271313/250000000000 : ℝ) (198368217051/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (269/2048 : ℝ)) 2 (991841085393/1000000000000 : ℝ) (198368217079/200000000000 : ℝ) (247960271313/250000000000 : ℝ) (198368217051/200000000000 : ℝ) (495920542661/500000000000 : ℝ) (39673643413/40000000000 : ℝ) (495920542661/500000000000 : ℝ) (39673643413/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (269/2048 : ℝ)) 3 (495920542661/500000000000 : ℝ) (39673643413/40000000000 : ℝ) (495920542661/500000000000 : ℝ) (39673643413/40000000000 : ℝ) (495920542661/500000000000 : ℝ) (39673643413/40000000000 : ℝ) (495920542661/500000000000 : ℝ) (39673643413/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (269/2048 : ℝ)) 4 (495920542661/500000000000 : ℝ) (39673643413/40000000000 : ℝ) (495920542661/500000000000 : ℝ) (39673643413/40000000000 : ℝ) (495920542661/500000000000 : ℝ) (39673643413/40000000000 : ℝ) (495920542661/500000000000 : ℝ) (39673643413/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (269/2048 : ℝ)) 5 (495920542661/500000000000 : ℝ) (39673643413/40000000000 : ℝ) (495920542661/500000000000 : ℝ) (39673643413/40000000000 : ℝ) (495920542661/500000000000 : ℝ) (39673643413/40000000000 : ℝ) (495920542661/500000000000 : ℝ) (39673643413/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (269/2048 : ℝ)) 6 (495920542661/500000000000 : ℝ) (39673643413/40000000000 : ℝ) (495920542661/500000000000 : ℝ) (39673643413/40000000000 : ℝ) (495920542661/500000000000 : ℝ) (39673643413/40000000000 : ℝ) (495920542661/500000000000 : ℝ) (39673643413/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (269/2048 : ℝ)) 7 (495920542661/500000000000 : ℝ) (39673643413/40000000000 : ℝ) (495920542661/500000000000 : ℝ) (39673643413/40000000000 : ℝ) (495920542661/500000000000 : ℝ) (39673643413/40000000000 : ℝ) (495920542661/500000000000 : ℝ) (39673643413/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (269/2048 : ℝ))) (17973212181/100000000000 : ℝ) (22466515227/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (269/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17973212181/100000000000 : ℝ) (22466515227/125000000000 : ℝ) (117973212181/200000000000 : ℝ) (147466515227/250000000000 : ℝ) (423948253693/1000000000000 : ℝ) (423948253701/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (269/2048 : ℝ))) 1 (117973212181/200000000000 : ℝ) (147466515227/250000000000 : ℝ) (423948253693/1000000000000 : ℝ) (423948253701/1000000000000 : ℝ) (506907157299/1000000000000 : ℝ) (101381431461/200000000000 : ℝ) (10001453623/20000000000 : ℝ) (500072681157/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (269/2048 : ℝ))) 2 (506907157299/1000000000000 : ℝ) (101381431461/200000000000 : ℝ) (10001453623/20000000000 : ℝ) (500072681157/1000000000000 : ℝ) (62936239903/125000000000 : ℝ) (503489919231/1000000000000 : ℝ) (503478322517/1000000000000 : ℝ) (125869580631/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (269/2048 : ℝ))) 3 (62936239903/125000000000 : ℝ) (503489919231/1000000000000 : ℝ) (503478322517/1000000000000 : ℝ) (125869580631/250000000000 : ℝ) (50348412087/100000000000 : ℝ) (251742060439/500000000000 : ℝ) (503484120837/1000000000000 : ℝ) (100696824169/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (269/2048 : ℝ))) 4 (50348412087/100000000000 : ℝ) (251742060439/500000000000 : ℝ) (503484120837/1000000000000 : ℝ) (100696824169/200000000000 : ℝ) (503484120853/1000000000000 : ℝ) (251742060431/500000000000 : ℝ) (503484120853/1000000000000 : ℝ) (251742060431/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (269/2048 : ℝ))) 5 (503484120853/1000000000000 : ℝ) (251742060431/500000000000 : ℝ) (503484120853/1000000000000 : ℝ) (251742060431/500000000000 : ℝ) (503484120853/1000000000000 : ℝ) (251742060431/500000000000 : ℝ) (503484120853/1000000000000 : ℝ) (251742060431/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (269/2048 : ℝ))) 6 (503484120853/1000000000000 : ℝ) (251742060431/500000000000 : ℝ) (503484120853/1000000000000 : ℝ) (251742060431/500000000000 : ℝ) (503484120853/1000000000000 : ℝ) (251742060431/500000000000 : ℝ) (503484120853/1000000000000 : ℝ) (251742060431/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (269/2048 : ℝ))) 7 (503484120853/1000000000000 : ℝ) (251742060431/500000000000 : ℝ) (503484120853/1000000000000 : ℝ) (251742060431/500000000000 : ℝ) (503484120853/1000000000000 : ℝ) (251742060431/500000000000 : ℝ) (503484120853/1000000000000 : ℝ) (251742060431/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (269/2048 : ℝ)) hmem 8 (495920542661/500000000000 : ℝ) (39673643413/40000000000 : ℝ) (495920542661/500000000000 : ℝ) (39673643413/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (269/2048 : ℝ))) hcmem 8 (503484120853/1000000000000 : ℝ) (251742060431/500000000000 : ℝ) (503484120853/1000000000000 : ℝ) (251742060431/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (269/2048 : ℝ)) (495920542661/500000000000 : ℝ) (39673643413/40000000000 : ℝ) (503484120853/1000000000000 : ℝ) (251742060431/500000000000 : ℝ) (797376736391/1000000000000 : ℝ) (797376736409/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1584_exp_lower
  have heNumeric : (256864446619/125000000000 : ℝ)/4 ≤ Real.exp (-5328476781897/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256864446619/125000000000 : ℝ)/4 ≤ Real.exp ((4303/32768 : ℝ)-(797376736409/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4303/32768 : ℝ) (269/2048 : ℝ) (797376736409/1000000000000 : ℝ) (256864446619/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1585; no trusted numerical premise.
theorem cover8_leaf1585_exp_radius : (498974660776984433/500000000000000000 : ℝ) ≤ Real.exp ((-4305/262144 : ℝ)/8) ∧ Real.exp ((-4305/262144 : ℝ)/8) ≤ (997949321553968867/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4305/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1585_exp_lower : (184022860168663001/200000000000000000 : ℝ) ≤ Real.exp ((-666059012873/1000000000000 : ℝ)/8) ∧ Real.exp ((-666059012873/1000000000000 : ℝ)/8) ≤ (460057150421657503/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666059012873/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1585_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054916774799/1000000000000 : ℝ) ≤ 4*Real.exp (269/2048 : ℝ)*Real.exp (-mu (radius 8 (4305/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054916774799/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4305/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1585_exp_radius
  have hrNumeric : (983711838639/1000000000000 : ℝ) ≤ Real.exp (-4305/262144 : ℝ) ∧ Real.exp (-4305/262144 : ℝ) ≤ (12296397983/12500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983711838639/1000000000000 : ℝ) ≤ (radius 8 (4305/32768 : ℝ)) ∧ (radius 8 (4305/32768 : ℝ)) ≤ (12296397983/12500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4305/32768 : ℝ)) (983711838639/1000000000000 : ℝ) (12296397983/12500000000 : ℝ) (179752659283/1000000000000 : ℝ) (17975265929/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4305/32768 : ℝ)) (983711838639/1000000000000 : ℝ) (12296397983/12500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4305/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983711838639/1000000000000 : ℝ) (12296397983/12500000000 : ℝ) (991855919319/1000000000000 : ℝ) (24796397983/25000000000 : ℝ) (99182248343/100000000000 : ℝ) (123977810429/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4305/32768 : ℝ)) 1 (991855919319/1000000000000 : ℝ) (24796397983/25000000000 : ℝ) (99182248343/100000000000 : ℝ) (123977810429/125000000000 : ℝ) (495919600687/500000000000 : ℝ) (30994975043/31250000000 : ℝ) (991839201233/1000000000000 : ℝ) (247959800309/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4305/32768 : ℝ)) 2 (495919600687/500000000000 : ℝ) (30994975043/31250000000 : ℝ) (991839201233/1000000000000 : ℝ) (247959800309/250000000000 : ℝ) (991839201303/1000000000000 : ℝ) (495919600653/500000000000 : ℝ) (991839201303/1000000000000 : ℝ) (495919600653/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4305/32768 : ℝ)) 3 (991839201303/1000000000000 : ℝ) (495919600653/500000000000 : ℝ) (991839201303/1000000000000 : ℝ) (495919600653/500000000000 : ℝ) (991839201303/1000000000000 : ℝ) (495919600653/500000000000 : ℝ) (991839201303/1000000000000 : ℝ) (495919600653/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4305/32768 : ℝ)) 4 (991839201303/1000000000000 : ℝ) (495919600653/500000000000 : ℝ) (991839201303/1000000000000 : ℝ) (495919600653/500000000000 : ℝ) (991839201303/1000000000000 : ℝ) (495919600653/500000000000 : ℝ) (991839201303/1000000000000 : ℝ) (495919600653/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4305/32768 : ℝ)) 5 (991839201303/1000000000000 : ℝ) (495919600653/500000000000 : ℝ) (991839201303/1000000000000 : ℝ) (495919600653/500000000000 : ℝ) (991839201303/1000000000000 : ℝ) (495919600653/500000000000 : ℝ) (991839201303/1000000000000 : ℝ) (495919600653/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4305/32768 : ℝ)) 6 (991839201303/1000000000000 : ℝ) (495919600653/500000000000 : ℝ) (991839201303/1000000000000 : ℝ) (495919600653/500000000000 : ℝ) (991839201303/1000000000000 : ℝ) (495919600653/500000000000 : ℝ) (991839201303/1000000000000 : ℝ) (495919600653/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4305/32768 : ℝ)) 7 (991839201303/1000000000000 : ℝ) (495919600653/500000000000 : ℝ) (991839201303/1000000000000 : ℝ) (495919600653/500000000000 : ℝ) (991839201303/1000000000000 : ℝ) (495919600653/500000000000 : ℝ) (991839201303/1000000000000 : ℝ) (495919600653/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4305/32768 : ℝ))) (179752659283/1000000000000 : ℝ) (17975265929/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4305/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (179752659283/1000000000000 : ℝ) (17975265929/100000000000 : ℝ) (589876329641/1000000000000 : ℝ) (117975265929/200000000000 : ℝ) (105993118669/250000000000 : ℝ) (84794494937/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4305/32768 : ℝ))) 1 (589876329641/1000000000000 : ℝ) (117975265929/200000000000 : ℝ) (105993118669/250000000000 : ℝ) (84794494937/200000000000 : ℝ) (253462201079/500000000000 : ℝ) (101384880433/200000000000 : ℝ) (500091318891/1000000000000 : ℝ) (500091318899/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4305/32768 : ℝ))) 2 (253462201079/500000000000 : ℝ) (101384880433/200000000000 : ℝ) (500091318891/1000000000000 : ℝ) (500091318899/1000000000000 : ℝ) (125876965131/250000000000 : ℝ) (125876965133/250000000000 : ℝ) (125874067239/250000000000 : ℝ) (100699253793/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4305/32768 : ℝ))) 3 (125876965131/250000000000 : ℝ) (125876965133/250000000000 : ℝ) (125874067239/250000000000 : ℝ) (100699253793/200000000000 : ℝ) (25175103237/50000000000 : ℝ) (503502064749/1000000000000 : ℝ) (251751032353/500000000000 : ℝ) (125875516179/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4305/32768 : ℝ))) 4 (25175103237/50000000000 : ℝ) (503502064749/1000000000000 : ℝ) (251751032353/500000000000 : ℝ) (125875516179/250000000000 : ℝ) (503502064723/1000000000000 : ℝ) (503502064733/1000000000000 : ℝ) (251751032361/500000000000 : ℝ) (503502064733/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4305/32768 : ℝ))) 5 (503502064723/1000000000000 : ℝ) (503502064733/1000000000000 : ℝ) (251751032361/500000000000 : ℝ) (503502064733/1000000000000 : ℝ) (251751032361/500000000000 : ℝ) (503502064733/1000000000000 : ℝ) (251751032361/500000000000 : ℝ) (503502064733/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4305/32768 : ℝ))) 6 (251751032361/500000000000 : ℝ) (503502064733/1000000000000 : ℝ) (251751032361/500000000000 : ℝ) (503502064733/1000000000000 : ℝ) (251751032361/500000000000 : ℝ) (503502064733/1000000000000 : ℝ) (251751032361/500000000000 : ℝ) (503502064733/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4305/32768 : ℝ))) 7 (251751032361/500000000000 : ℝ) (503502064733/1000000000000 : ℝ) (251751032361/500000000000 : ℝ) (503502064733/1000000000000 : ℝ) (251751032361/500000000000 : ℝ) (503502064733/1000000000000 : ℝ) (251751032361/500000000000 : ℝ) (503502064733/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4305/32768 : ℝ)) hmem 8 (991839201303/1000000000000 : ℝ) (495919600653/500000000000 : ℝ) (991839201303/1000000000000 : ℝ) (495919600653/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4305/32768 : ℝ))) hcmem 8 (251751032361/500000000000 : ℝ) (503502064733/1000000000000 : ℝ) (251751032361/500000000000 : ℝ) (503502064733/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4305/32768 : ℝ)) (991839201303/1000000000000 : ℝ) (495919600653/500000000000 : ℝ) (251751032361/500000000000 : ℝ) (503502064733/1000000000000 : ℝ) (398703334551/500000000000 : ℝ) (797406669123/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1585_exp_lower
  have heNumeric : (2054916774799/1000000000000 : ℝ)/4 ≤ Real.exp (-666059012873/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054916774799/1000000000000 : ℝ)/4 ≤ Real.exp ((269/2048 : ℝ)-(797406669123/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (269/2048 : ℝ) (4305/32768 : ℝ) (797406669123/1000000000000 : ℝ) (2054916774799/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1586; no trusted numerical premise.
theorem cover8_leaf1586_exp_radius : (997948845694763799/1000000000000000000 : ℝ) ≤ Real.exp ((-2153/131072 : ℝ)/8) ∧ Real.exp ((-2153/131072 : ℝ)/8) ≤ (4989744228473819/5000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2153/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1586_exp_lower : (230028592163277631/250000000000000000 : ℝ) ≤ Real.exp ((-5328467386367/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328467386367/8000000000000 : ℝ)/8) ≤ (36804574746124421/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328467386367/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1586_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054917986331/1000000000000 : ℝ) ≤ 4*Real.exp (4305/32768 : ℝ)*Real.exp (-mu (radius 8 (2153/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054917986331/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2153/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1586_exp_radius
  have hrNumeric : (245927021521/250000000000 : ℝ) ≤ Real.exp (-2153/131072 : ℝ) ∧ Real.exp (-2153/131072 : ℝ) ≤ (196741617217/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245927021521/250000000000 : ℝ) ≤ (radius 8 (2153/16384 : ℝ)) ∧ (radius 8 (2153/16384 : ℝ)) ≤ (196741617217/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2153/16384 : ℝ)) (245927021521/250000000000 : ℝ) (196741617217/200000000000 : ℝ) (719092777/4000000000 : ℝ) (11235824641/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2153/16384 : ℝ)) (245927021521/250000000000 : ℝ) (196741617217/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2153/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245927021521/250000000000 : ℝ) (196741617217/200000000000 : ℝ) (495927021521/500000000000 : ℝ) (991854043043/1000000000000 : ℝ) (991820591681/1000000000000 : ℝ) (991820591683/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2153/16384 : ℝ)) 1 (495927021521/500000000000 : ℝ) (991854043043/1000000000000 : ℝ) (991820591681/1000000000000 : ℝ) (991820591683/1000000000000 : ℝ) (991837317361/1000000000000 : ℝ) (991837317363/1000000000000 : ℝ) (49591865861/50000000000 : ℝ) (495918658611/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2153/16384 : ℝ)) 2 (991837317361/1000000000000 : ℝ) (991837317363/1000000000000 : ℝ) (49591865861/50000000000 : ℝ) (495918658611/500000000000 : ℝ) (99183731729/100000000000 : ℝ) (991837317293/1000000000000 : ℝ) (99183731729/100000000000 : ℝ) (991837317293/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2153/16384 : ℝ)) 3 (99183731729/100000000000 : ℝ) (991837317293/1000000000000 : ℝ) (99183731729/100000000000 : ℝ) (991837317293/1000000000000 : ℝ) (99183731729/100000000000 : ℝ) (991837317293/1000000000000 : ℝ) (99183731729/100000000000 : ℝ) (991837317293/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2153/16384 : ℝ)) 4 (99183731729/100000000000 : ℝ) (991837317293/1000000000000 : ℝ) (99183731729/100000000000 : ℝ) (991837317293/1000000000000 : ℝ) (99183731729/100000000000 : ℝ) (991837317293/1000000000000 : ℝ) (99183731729/100000000000 : ℝ) (991837317293/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2153/16384 : ℝ)) 5 (99183731729/100000000000 : ℝ) (991837317293/1000000000000 : ℝ) (99183731729/100000000000 : ℝ) (991837317293/1000000000000 : ℝ) (99183731729/100000000000 : ℝ) (991837317293/1000000000000 : ℝ) (99183731729/100000000000 : ℝ) (991837317293/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2153/16384 : ℝ)) 6 (99183731729/100000000000 : ℝ) (991837317293/1000000000000 : ℝ) (99183731729/100000000000 : ℝ) (991837317293/1000000000000 : ℝ) (99183731729/100000000000 : ℝ) (991837317293/1000000000000 : ℝ) (99183731729/100000000000 : ℝ) (991837317293/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2153/16384 : ℝ)) 7 (99183731729/100000000000 : ℝ) (991837317293/1000000000000 : ℝ) (99183731729/100000000000 : ℝ) (991837317293/1000000000000 : ℝ) (99183731729/100000000000 : ℝ) (991837317293/1000000000000 : ℝ) (99183731729/100000000000 : ℝ) (991837317293/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2153/16384 : ℝ))) (719092777/4000000000 : ℝ) (11235824641/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2153/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (719092777/4000000000 : ℝ) (11235824641/62500000000 : ℝ) (4719092777/8000000000 : ℝ) (73735824641/125000000000 : ℝ) (423996691319/1000000000000 : ℝ) (423996691327/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2153/16384 : ℝ))) 1 (4719092777/8000000000 : ℝ) (73735824641/125000000000 : ℝ) (423996691319/1000000000000 : ℝ) (423996691327/1000000000000 : ℝ) (253470822111/500000000000 : ℝ) (126735411057/250000000000 : ℝ) (7814218021/15625000000 : ℝ) (500109953351/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2153/16384 : ℝ))) 2 (253470822111/500000000000 : ℝ) (126735411057/250000000000 : ℝ) (7814218021/15625000000 : ℝ) (500109953351/1000000000000 : ℝ) (503525798783/1000000000000 : ℝ) (50352579879/100000000000 : ℝ) (503514212351/1000000000000 : ℝ) (503514212359/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2153/16384 : ℝ))) 3 (503525798783/1000000000000 : ℝ) (50352579879/100000000000 : ℝ) (503514212351/1000000000000 : ℝ) (503514212359/1000000000000 : ℝ) (503520005567/1000000000000 : ℝ) (20140800223/40000000000 : ℝ) (503520005533/1000000000000 : ℝ) (251760002771/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2153/16384 : ℝ))) 4 (503520005567/1000000000000 : ℝ) (20140800223/40000000000 : ℝ) (503520005533/1000000000000 : ℝ) (251760002771/500000000000 : ℝ) (10070400111/20000000000 : ℝ) (503520005559/1000000000000 : ℝ) (503520005549/1000000000000 : ℝ) (503520005559/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2153/16384 : ℝ))) 5 (10070400111/20000000000 : ℝ) (503520005559/1000000000000 : ℝ) (503520005549/1000000000000 : ℝ) (503520005559/1000000000000 : ℝ) (503520005549/1000000000000 : ℝ) (503520005559/1000000000000 : ℝ) (503520005549/1000000000000 : ℝ) (503520005559/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2153/16384 : ℝ))) 6 (503520005549/1000000000000 : ℝ) (503520005559/1000000000000 : ℝ) (503520005549/1000000000000 : ℝ) (503520005559/1000000000000 : ℝ) (503520005549/1000000000000 : ℝ) (503520005559/1000000000000 : ℝ) (503520005549/1000000000000 : ℝ) (503520005559/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2153/16384 : ℝ))) 7 (503520005549/1000000000000 : ℝ) (503520005559/1000000000000 : ℝ) (503520005549/1000000000000 : ℝ) (503520005559/1000000000000 : ℝ) (503520005549/1000000000000 : ℝ) (503520005559/1000000000000 : ℝ) (503520005549/1000000000000 : ℝ) (503520005559/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2153/16384 : ℝ)) hmem 8 (99183731729/100000000000 : ℝ) (991837317293/1000000000000 : ℝ) (99183731729/100000000000 : ℝ) (991837317293/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2153/16384 : ℝ))) hcmem 8 (503520005549/1000000000000 : ℝ) (503520005559/1000000000000 : ℝ) (503520005549/1000000000000 : ℝ) (503520005559/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2153/16384 : ℝ)) (99183731729/100000000000 : ℝ) (991837317293/1000000000000 : ℝ) (503520005549/1000000000000 : ℝ) (503520005559/1000000000000 : ℝ) (159487319421/200000000000 : ℝ) (199359149281/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1586_exp_lower
  have heNumeric : (2054917986331/1000000000000 : ℝ)/4 ≤ Real.exp (-5328467386367/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054917986331/1000000000000 : ℝ)/4 ≤ Real.exp ((4305/32768 : ℝ)-(199359149281/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4305/32768 : ℝ) (2153/16384 : ℝ) (199359149281/250000000000 : ℝ) (2054917986331/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1587; no trusted numerical premise.
theorem cover8_leaf1587_exp_radius : (24948709245894641/25000000000000000 : ℝ) ≤ Real.exp ((-4307/262144 : ℝ)/8) ∧ Real.exp ((-4307/262144 : ℝ)/8) ≤ (997948369835785641/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4307/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1587_exp_lower : (230028609250668293/250000000000000000 : ℝ) ≤ Real.exp ((-2664231316103/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664231316103/4000000000000 : ℝ)/8) ≤ (920114437002673173/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664231316103/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1587_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513729801877/250000000000 : ℝ) ≤ 4*Real.exp (2153/16384 : ℝ)*Real.exp (-mu (radius 8 (4307/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (513729801877/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4307/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1587_exp_radius
  have hrNumeric : (491852166771/500000000000 : ℝ) ≤ Real.exp (-4307/262144 : ℝ) ∧ Real.exp (-4307/262144 : ℝ) ≤ (983704333543/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491852166771/500000000000 : ℝ) ≤ (radius 8 (4307/32768 : ℝ)) ∧ (radius 8 (4307/32768 : ℝ)) ≤ (983704333543/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4307/32768 : ℝ)) (491852166771/500000000000 : ℝ) (983704333543/1000000000000 : ℝ) (89896863361/500000000000 : ℝ) (22474215841/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4307/32768 : ℝ)) (491852166771/500000000000 : ℝ) (983704333543/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4307/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491852166771/500000000000 : ℝ) (983704333543/1000000000000 : ℝ) (991852166771/1000000000000 : ℝ) (247963041693/250000000000 : ℝ) (198363739987/200000000000 : ℝ) (991818699937/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4307/32768 : ℝ)) 1 (991852166771/1000000000000 : ℝ) (247963041693/250000000000 : ℝ) (198363739987/200000000000 : ℝ) (991818699937/1000000000000 : ℝ) (991835433353/1000000000000 : ℝ) (198367086671/200000000000 : ℝ) (991835433211/1000000000000 : ℝ) (495917716607/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4307/32768 : ℝ)) 2 (991835433353/1000000000000 : ℝ) (198367086671/200000000000 : ℝ) (991835433211/1000000000000 : ℝ) (495917716607/500000000000 : ℝ) (495917716641/500000000000 : ℝ) (198367086657/200000000000 : ℝ) (991835433281/1000000000000 : ℝ) (198367086657/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4307/32768 : ℝ)) 3 (495917716641/500000000000 : ℝ) (198367086657/200000000000 : ℝ) (991835433281/1000000000000 : ℝ) (198367086657/200000000000 : ℝ) (991835433281/1000000000000 : ℝ) (198367086657/200000000000 : ℝ) (991835433281/1000000000000 : ℝ) (198367086657/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4307/32768 : ℝ)) 4 (991835433281/1000000000000 : ℝ) (198367086657/200000000000 : ℝ) (991835433281/1000000000000 : ℝ) (198367086657/200000000000 : ℝ) (991835433281/1000000000000 : ℝ) (198367086657/200000000000 : ℝ) (991835433281/1000000000000 : ℝ) (198367086657/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4307/32768 : ℝ)) 5 (991835433281/1000000000000 : ℝ) (198367086657/200000000000 : ℝ) (991835433281/1000000000000 : ℝ) (198367086657/200000000000 : ℝ) (991835433281/1000000000000 : ℝ) (198367086657/200000000000 : ℝ) (991835433281/1000000000000 : ℝ) (198367086657/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4307/32768 : ℝ)) 6 (991835433281/1000000000000 : ℝ) (198367086657/200000000000 : ℝ) (991835433281/1000000000000 : ℝ) (198367086657/200000000000 : ℝ) (991835433281/1000000000000 : ℝ) (198367086657/200000000000 : ℝ) (991835433281/1000000000000 : ℝ) (198367086657/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4307/32768 : ℝ)) 7 (991835433281/1000000000000 : ℝ) (198367086657/200000000000 : ℝ) (991835433281/1000000000000 : ℝ) (198367086657/200000000000 : ℝ) (991835433281/1000000000000 : ℝ) (198367086657/200000000000 : ℝ) (991835433281/1000000000000 : ℝ) (198367086657/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4307/32768 : ℝ))) (89896863361/500000000000 : ℝ) (22474215841/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4307/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89896863361/500000000000 : ℝ) (22474215841/125000000000 : ℝ) (589896863361/1000000000000 : ℝ) (147474215841/250000000000 : ℝ) (212010451819/500000000000 : ℝ) (212010451823/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4307/32768 : ℝ))) 1 (589896863361/1000000000000 : ℝ) (147474215841/250000000000 : ℝ) (212010451819/500000000000 : ℝ) (212010451823/500000000000 : ℝ) (506958883499/1000000000000 : ℝ) (101391776701/200000000000 : ℝ) (500128584521/1000000000000 : ℝ) (31258036533/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4307/32768 : ℝ))) 2 (506958883499/1000000000000 : ℝ) (101391776701/200000000000 : ℝ) (500128584521/1000000000000 : ℝ) (31258036533/62500000000 : ℝ) (50354373401/100000000000 : ℝ) (503543734017/1000000000000 : ℝ) (503532152711/1000000000000 : ℝ) (503532152719/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4307/32768 : ℝ))) 3 (50354373401/100000000000 : ℝ) (503543734017/1000000000000 : ℝ) (503532152711/1000000000000 : ℝ) (503532152719/1000000000000 : ℝ) (1573556073/3125000000 : ℝ) (62942242921/125000000000 : ℝ) (503537943327/1000000000000 : ℝ) (100707588667/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4307/32768 : ℝ))) 4 (1573556073/3125000000 : ℝ) (62942242921/125000000000 : ℝ) (503537943327/1000000000000 : ℝ) (100707588667/200000000000 : ℝ) (503537943343/1000000000000 : ℝ) (62942242919/125000000000 : ℝ) (503537943343/1000000000000 : ℝ) (62942242919/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4307/32768 : ℝ))) 5 (503537943343/1000000000000 : ℝ) (62942242919/125000000000 : ℝ) (503537943343/1000000000000 : ℝ) (62942242919/125000000000 : ℝ) (503537943343/1000000000000 : ℝ) (62942242919/125000000000 : ℝ) (503537943343/1000000000000 : ℝ) (62942242919/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4307/32768 : ℝ))) 6 (503537943343/1000000000000 : ℝ) (62942242919/125000000000 : ℝ) (503537943343/1000000000000 : ℝ) (62942242919/125000000000 : ℝ) (503537943343/1000000000000 : ℝ) (62942242919/125000000000 : ℝ) (503537943343/1000000000000 : ℝ) (62942242919/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4307/32768 : ℝ))) 7 (503537943343/1000000000000 : ℝ) (62942242919/125000000000 : ℝ) (503537943343/1000000000000 : ℝ) (62942242919/125000000000 : ℝ) (503537943343/1000000000000 : ℝ) (62942242919/125000000000 : ℝ) (503537943343/1000000000000 : ℝ) (62942242919/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4307/32768 : ℝ)) hmem 8 (991835433281/1000000000000 : ℝ) (198367086657/200000000000 : ℝ) (991835433281/1000000000000 : ℝ) (198367086657/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4307/32768 : ℝ))) hcmem 8 (503537943343/1000000000000 : ℝ) (62942242919/125000000000 : ℝ) (503537943343/1000000000000 : ℝ) (62942242919/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4307/32768 : ℝ)) (991835433281/1000000000000 : ℝ) (198367086657/200000000000 : ℝ) (503537943343/1000000000000 : ℝ) (62942242919/125000000000 : ℝ) (797466520413/1000000000000 : ℝ) (49841657527/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1587_exp_lower
  have heNumeric : (513729801877/250000000000 : ℝ)/4 ≤ Real.exp (-2664231316103/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513729801877/250000000000 : ℝ)/4 ≤ Real.exp ((2153/16384 : ℝ)-(49841657527/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2153/16384 : ℝ) (4307/32768 : ℝ) (49841657527/62500000000 : ℝ) (513729801877/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1588; no trusted numerical premise.
theorem cover8_leaf1588_exp_radius : (997947893977034387/1000000000000000000 : ℝ) ≤ Real.exp ((-1077/65536 : ℝ)/8) ∧ Real.exp ((-1077/65536 : ℝ)/8) ≤ (249486973494258597/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1077/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1588_exp_lower : (920114505893613269/1000000000000000000 : ℝ) ≤ Real.exp ((-5328457840389/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328457840389/8000000000000 : ℝ)/8) ≤ (92011450589361327/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328457840389/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1588_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027460219179/500000000000 : ℝ) ≤ 4*Real.exp (4307/32768 : ℝ)*Real.exp (-mu (radius 8 (1077/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (1027460219179/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1077/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1588_exp_radius
  have hrNumeric : (196740116203/200000000000 : ℝ) ≤ Real.exp (-1077/65536 : ℝ) ∧ Real.exp (-1077/65536 : ℝ) ≤ (122962572627/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196740116203/200000000000 : ℝ) ≤ (radius 8 (1077/8192 : ℝ)) ∧ (radius 8 (1077/8192 : ℝ)) ≤ (122962572627/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1077/8192 : ℝ)) (196740116203/200000000000 : ℝ) (122962572627/125000000000 : ℝ) (179814256689/1000000000000 : ℝ) (35962851339/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1077/8192 : ℝ)) (196740116203/200000000000 : ℝ) (122962572627/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1077/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196740116203/200000000000 : ℝ) (122962572627/125000000000 : ℝ) (991850290507/1000000000000 : ℝ) (247962572627/250000000000 : ℝ) (991816808193/1000000000000 : ℝ) (495908404097/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1077/8192 : ℝ)) 1 (991850290507/1000000000000 : ℝ) (247962572627/250000000000 : ℝ) (991816808193/1000000000000 : ℝ) (495908404097/500000000000 : ℝ) (19836670987/20000000000 : ℝ) (991833549351/1000000000000 : ℝ) (123979193651/125000000000 : ℝ) (99183354921/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1077/8192 : ℝ)) 2 (19836670987/20000000000 : ℝ) (991833549351/1000000000000 : ℝ) (123979193651/125000000000 : ℝ) (99183354921/100000000000 : ℝ) (991833549279/1000000000000 : ℝ) (991833549281/1000000000000 : ℝ) (495916774639/500000000000 : ℝ) (991833549281/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1077/8192 : ℝ)) 3 (991833549279/1000000000000 : ℝ) (991833549281/1000000000000 : ℝ) (495916774639/500000000000 : ℝ) (991833549281/1000000000000 : ℝ) (495916774639/500000000000 : ℝ) (991833549281/1000000000000 : ℝ) (495916774639/500000000000 : ℝ) (991833549281/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1077/8192 : ℝ)) 4 (495916774639/500000000000 : ℝ) (991833549281/1000000000000 : ℝ) (495916774639/500000000000 : ℝ) (991833549281/1000000000000 : ℝ) (495916774639/500000000000 : ℝ) (991833549281/1000000000000 : ℝ) (495916774639/500000000000 : ℝ) (991833549281/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1077/8192 : ℝ)) 5 (495916774639/500000000000 : ℝ) (991833549281/1000000000000 : ℝ) (495916774639/500000000000 : ℝ) (991833549281/1000000000000 : ℝ) (495916774639/500000000000 : ℝ) (991833549281/1000000000000 : ℝ) (495916774639/500000000000 : ℝ) (991833549281/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1077/8192 : ℝ)) 6 (495916774639/500000000000 : ℝ) (991833549281/1000000000000 : ℝ) (495916774639/500000000000 : ℝ) (991833549281/1000000000000 : ℝ) (495916774639/500000000000 : ℝ) (991833549281/1000000000000 : ℝ) (495916774639/500000000000 : ℝ) (991833549281/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1077/8192 : ℝ)) 7 (495916774639/500000000000 : ℝ) (991833549281/1000000000000 : ℝ) (495916774639/500000000000 : ℝ) (991833549281/1000000000000 : ℝ) (495916774639/500000000000 : ℝ) (991833549281/1000000000000 : ℝ) (495916774639/500000000000 : ℝ) (991833549281/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1077/8192 : ℝ))) (179814256689/1000000000000 : ℝ) (35962851339/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1077/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (179814256689/1000000000000 : ℝ) (35962851339/200000000000 : ℝ) (73738391043/125000000000 : ℝ) (147476782087/250000000000 : ℝ) (21202255581/50000000000 : ℝ) (106011277907/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1077/8192 : ℝ))) 1 (73738391043/125000000000 : ℝ) (147476782087/250000000000 : ℝ) (21202255581/50000000000 : ℝ) (106011277907/250000000000 : ℝ) (253488059991/500000000000 : ℝ) (126744029997/250000000000 : ℝ) (125036803103/250000000000 : ℝ) (500147212419/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1077/8192 : ℝ))) 2 (253488059991/500000000000 : ℝ) (126744029997/250000000000 : ℝ) (125036803103/250000000000 : ℝ) (500147212419/1000000000000 : ℝ) (503561666197/1000000000000 : ℝ) (125890416551/250000000000 : ℝ) (503550090029/1000000000000 : ℝ) (125887522509/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1077/8192 : ℝ))) 3 (503561666197/1000000000000 : ℝ) (125890416551/250000000000 : ℝ) (503550090029/1000000000000 : ℝ) (125887522509/250000000000 : ℝ) (503555878113/1000000000000 : ℝ) (12588896953/25000000000 : ℝ) (503555878079/1000000000000 : ℝ) (503555878087/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1077/8192 : ℝ))) 4 (503555878113/1000000000000 : ℝ) (12588896953/25000000000 : ℝ) (503555878079/1000000000000 : ℝ) (503555878087/1000000000000 : ℝ) (31472242381/62500000000 : ℝ) (62944484763/125000000000 : ℝ) (100711175619/200000000000 : ℝ) (62944484763/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1077/8192 : ℝ))) 5 (31472242381/62500000000 : ℝ) (62944484763/125000000000 : ℝ) (100711175619/200000000000 : ℝ) (62944484763/125000000000 : ℝ) (100711175619/200000000000 : ℝ) (62944484763/125000000000 : ℝ) (100711175619/200000000000 : ℝ) (62944484763/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1077/8192 : ℝ))) 6 (100711175619/200000000000 : ℝ) (62944484763/125000000000 : ℝ) (100711175619/200000000000 : ℝ) (62944484763/125000000000 : ℝ) (100711175619/200000000000 : ℝ) (62944484763/125000000000 : ℝ) (100711175619/200000000000 : ℝ) (62944484763/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1077/8192 : ℝ))) 7 (100711175619/200000000000 : ℝ) (62944484763/125000000000 : ℝ) (100711175619/200000000000 : ℝ) (62944484763/125000000000 : ℝ) (100711175619/200000000000 : ℝ) (62944484763/125000000000 : ℝ) (100711175619/200000000000 : ℝ) (62944484763/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1077/8192 : ℝ)) hmem 8 (495916774639/500000000000 : ℝ) (991833549281/1000000000000 : ℝ) (495916774639/500000000000 : ℝ) (991833549281/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1077/8192 : ℝ))) hcmem 8 (100711175619/200000000000 : ℝ) (62944484763/125000000000 : ℝ) (100711175619/200000000000 : ℝ) (62944484763/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1077/8192 : ℝ)) (495916774639/500000000000 : ℝ) (991833549281/1000000000000 : ℝ) (100711175619/200000000000 : ℝ) (62944484763/125000000000 : ℝ) (159499287803/200000000000 : ℝ) (797496439033/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1588_exp_lower
  have heNumeric : (1027460219179/500000000000 : ℝ)/4 ≤ Real.exp (-5328457840389/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027460219179/500000000000 : ℝ)/4 ≤ Real.exp ((4307/32768 : ℝ)-(797496439033/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4307/32768 : ℝ) (1077/8192 : ℝ) (797496439033/1000000000000 : ℝ) (1027460219179/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1589; no trusted numerical premise.
theorem cover8_leaf1589_exp_radius : (498973709059255021/500000000000000000 : ℝ) ≤ Real.exp ((-4309/262144 : ℝ)/8) ∧ Real.exp ((-4309/262144 : ℝ)/8) ≤ (997947418118510043/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4309/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1589_exp_lower : (920114575325700909/1000000000000000000 : ℝ) ≤ Real.exp ((-1332113252733/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332113252733/2000000000000 : ℝ)/8) ≤ (92011457532570091/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332113252733/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1589_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054921678877/1000000000000 : ℝ) ≤ 4*Real.exp (1077/8192 : ℝ)*Real.exp (-mu (radius 8 (4309/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054921678877/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4309/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1589_exp_radius
  have hrNumeric : (983696828503/1000000000000 : ℝ) ≤ Real.exp (-4309/262144 : ℝ) ∧ Real.exp (-4309/262144 : ℝ) ≤ (122962103563/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983696828503/1000000000000 : ℝ) ≤ (radius 8 (4309/32768 : ℝ)) ∧ (radius 8 (4309/32768 : ℝ)) ≤ (122962103563/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4309/32768 : ℝ)) (983696828503/1000000000000 : ℝ) (122962103563/125000000000 : ℝ) (22479348019/125000000000 : ℝ) (89917392079/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4309/32768 : ℝ)) (983696828503/1000000000000 : ℝ) (122962103563/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4309/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983696828503/1000000000000 : ℝ) (122962103563/125000000000 : ℝ) (991848414251/1000000000000 : ℝ) (247962103563/250000000000 : ℝ) (198362983291/200000000000 : ℝ) (123976864557/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4309/32768 : ℝ)) 1 (991848414251/1000000000000 : ℝ) (247962103563/250000000000 : ℝ) (198362983291/200000000000 : ℝ) (123976864557/125000000000 : ℝ) (991831665353/1000000000000 : ℝ) (495915832677/500000000000 : ℝ) (991831665211/1000000000000 : ℝ) (991831665213/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4309/32768 : ℝ)) 2 (991831665353/1000000000000 : ℝ) (495915832677/500000000000 : ℝ) (991831665211/1000000000000 : ℝ) (991831665213/1000000000000 : ℝ) (495915832641/500000000000 : ℝ) (247957916321/250000000000 : ℝ) (991831665281/1000000000000 : ℝ) (247957916321/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4309/32768 : ℝ)) 3 (495915832641/500000000000 : ℝ) (247957916321/250000000000 : ℝ) (991831665281/1000000000000 : ℝ) (247957916321/250000000000 : ℝ) (991831665281/1000000000000 : ℝ) (247957916321/250000000000 : ℝ) (991831665281/1000000000000 : ℝ) (247957916321/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4309/32768 : ℝ)) 4 (991831665281/1000000000000 : ℝ) (247957916321/250000000000 : ℝ) (991831665281/1000000000000 : ℝ) (247957916321/250000000000 : ℝ) (991831665281/1000000000000 : ℝ) (247957916321/250000000000 : ℝ) (991831665281/1000000000000 : ℝ) (247957916321/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4309/32768 : ℝ)) 5 (991831665281/1000000000000 : ℝ) (247957916321/250000000000 : ℝ) (991831665281/1000000000000 : ℝ) (247957916321/250000000000 : ℝ) (991831665281/1000000000000 : ℝ) (247957916321/250000000000 : ℝ) (991831665281/1000000000000 : ℝ) (247957916321/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4309/32768 : ℝ)) 6 (991831665281/1000000000000 : ℝ) (247957916321/250000000000 : ℝ) (991831665281/1000000000000 : ℝ) (247957916321/250000000000 : ℝ) (991831665281/1000000000000 : ℝ) (247957916321/250000000000 : ℝ) (991831665281/1000000000000 : ℝ) (247957916321/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4309/32768 : ℝ)) 7 (991831665281/1000000000000 : ℝ) (247957916321/250000000000 : ℝ) (991831665281/1000000000000 : ℝ) (247957916321/250000000000 : ℝ) (991831665281/1000000000000 : ℝ) (247957916321/250000000000 : ℝ) (991831665281/1000000000000 : ℝ) (247957916321/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4309/32768 : ℝ))) (22479348019/125000000000 : ℝ) (89917392079/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4309/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22479348019/125000000000 : ℝ) (89917392079/500000000000 : ℝ) (147479348019/250000000000 : ℝ) (589917392079/1000000000000 : ℝ) (106017328817/250000000000 : ℝ) (106017328819/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4309/32768 : ℝ))) 1 (147479348019/250000000000 : ℝ) (589917392079/1000000000000 : ℝ) (106017328817/250000000000 : ℝ) (106017328819/250000000000 : ℝ) (63374169209/125000000000 : ℝ) (253496676839/500000000000 : ℝ) (25008291851/50000000000 : ℝ) (500165837027/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4309/32768 : ℝ))) 2 (63374169209/125000000000 : ℝ) (253496676839/500000000000 : ℝ) (25008291851/50000000000 : ℝ) (500165837027/1000000000000 : ℝ) (251789797673/500000000000 : ℝ) (503579595353/1000000000000 : ℝ) (100713604861/200000000000 : ℝ) (62946003039/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4309/32768 : ℝ))) 3 (251789797673/500000000000 : ℝ) (503579595353/1000000000000 : ℝ) (100713604861/200000000000 : ℝ) (62946003039/125000000000 : ℝ) (20142952393/40000000000 : ℝ) (503573809833/1000000000000 : ℝ) (3934170389/7812500000 : ℝ) (2517869049/5000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4309/32768 : ℝ))) 4 (20142952393/40000000000 : ℝ) (503573809833/1000000000000 : ℝ) (3934170389/7812500000 : ℝ) (2517869049/5000000000 : ℝ) (31473363113/62500000000 : ℝ) (503573809817/1000000000000 : ℝ) (31473363113/62500000000 : ℝ) (503573809817/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4309/32768 : ℝ))) 5 (31473363113/62500000000 : ℝ) (503573809817/1000000000000 : ℝ) (31473363113/62500000000 : ℝ) (503573809817/1000000000000 : ℝ) (31473363113/62500000000 : ℝ) (503573809817/1000000000000 : ℝ) (31473363113/62500000000 : ℝ) (503573809817/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4309/32768 : ℝ))) 6 (31473363113/62500000000 : ℝ) (503573809817/1000000000000 : ℝ) (31473363113/62500000000 : ℝ) (503573809817/1000000000000 : ℝ) (31473363113/62500000000 : ℝ) (503573809817/1000000000000 : ℝ) (31473363113/62500000000 : ℝ) (503573809817/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4309/32768 : ℝ))) 7 (31473363113/62500000000 : ℝ) (503573809817/1000000000000 : ℝ) (31473363113/62500000000 : ℝ) (503573809817/1000000000000 : ℝ) (31473363113/62500000000 : ℝ) (503573809817/1000000000000 : ℝ) (31473363113/62500000000 : ℝ) (503573809817/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4309/32768 : ℝ)) hmem 8 (991831665281/1000000000000 : ℝ) (247957916321/250000000000 : ℝ) (991831665281/1000000000000 : ℝ) (247957916321/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4309/32768 : ℝ))) hcmem 8 (31473363113/62500000000 : ℝ) (503573809817/1000000000000 : ℝ) (31473363113/62500000000 : ℝ) (503573809817/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4309/32768 : ℝ)) (991831665281/1000000000000 : ℝ) (247957916321/250000000000 : ℝ) (31473363113/62500000000 : ℝ) (503573809817/1000000000000 : ℝ) (797526352911/1000000000000 : ℝ) (797526352929/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1589_exp_lower
  have heNumeric : (2054921678877/1000000000000 : ℝ)/4 ≤ Real.exp (-1332113252733/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054921678877/1000000000000 : ℝ)/4 ≤ Real.exp ((1077/8192 : ℝ)-(797526352929/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1077/8192 : ℝ) (4309/32768 : ℝ) (797526352929/1000000000000 : ℝ) (2054921678877/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1590; no trusted numerical premise.
theorem cover8_leaf1590_exp_radius : (249486735565053151/250000000000000000 : ℝ) ≤ Real.exp ((-2155/131072 : ℝ)/8) ∧ Real.exp ((-2155/131072 : ℝ)/8) ≤ (199589388452042521/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2155/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1590_exp_lower : (92011464529698097/100000000000000000 : ℝ) ≤ Real.exp ((-5328448143971/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328448143971/8000000000000 : ℝ)/8) ≤ (920114645296980971/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328448143971/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1590_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205492292903/100000000000 : ℝ) ≤ 4*Real.exp (4309/32768 : ℝ)*Real.exp (-mu (radius 8 (2155/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (205492292903/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2155/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1590_exp_radius
  have hrNumeric : (245923269001/250000000000 : ℝ) ≤ Real.exp (-2155/131072 : ℝ) ∧ Real.exp (-2155/131072 : ℝ) ≤ (196738615201/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245923269001/250000000000 : ℝ) ≤ (radius 8 (2155/16384 : ℝ)) ∧ (radius 8 (2155/16384 : ℝ)) ≤ (196738615201/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2155/16384 : ℝ)) (245923269001/250000000000 : ℝ) (196738615201/200000000000 : ℝ) (179855309123/1000000000000 : ℝ) (179855309129/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2155/16384 : ℝ)) (245923269001/250000000000 : ℝ) (196738615201/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2155/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245923269001/250000000000 : ℝ) (196738615201/200000000000 : ℝ) (495923269001/500000000000 : ℝ) (991846538003/1000000000000 : ℝ) (991813024719/1000000000000 : ℝ) (991813024721/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2155/16384 : ℝ)) 1 (495923269001/500000000000 : ℝ) (991846538003/1000000000000 : ℝ) (991813024719/1000000000000 : ℝ) (991813024721/1000000000000 : ℝ) (12397872267/12500000000 : ℝ) (495914890681/500000000000 : ℝ) (495914890609/500000000000 : ℝ) (991829781221/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2155/16384 : ℝ)) 2 (12397872267/12500000000 : ℝ) (495914890681/500000000000 : ℝ) (495914890609/500000000000 : ℝ) (991829781221/1000000000000 : ℝ) (991829781289/1000000000000 : ℝ) (247957445323/250000000000 : ℝ) (123978722661/125000000000 : ℝ) (247957445323/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2155/16384 : ℝ)) 3 (991829781289/1000000000000 : ℝ) (247957445323/250000000000 : ℝ) (123978722661/125000000000 : ℝ) (247957445323/250000000000 : ℝ) (123978722661/125000000000 : ℝ) (247957445323/250000000000 : ℝ) (123978722661/125000000000 : ℝ) (247957445323/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2155/16384 : ℝ)) 4 (123978722661/125000000000 : ℝ) (247957445323/250000000000 : ℝ) (123978722661/125000000000 : ℝ) (247957445323/250000000000 : ℝ) (123978722661/125000000000 : ℝ) (247957445323/250000000000 : ℝ) (123978722661/125000000000 : ℝ) (247957445323/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2155/16384 : ℝ)) 5 (123978722661/125000000000 : ℝ) (247957445323/250000000000 : ℝ) (123978722661/125000000000 : ℝ) (247957445323/250000000000 : ℝ) (123978722661/125000000000 : ℝ) (247957445323/250000000000 : ℝ) (123978722661/125000000000 : ℝ) (247957445323/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2155/16384 : ℝ)) 6 (123978722661/125000000000 : ℝ) (247957445323/250000000000 : ℝ) (123978722661/125000000000 : ℝ) (247957445323/250000000000 : ℝ) (123978722661/125000000000 : ℝ) (247957445323/250000000000 : ℝ) (123978722661/125000000000 : ℝ) (247957445323/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2155/16384 : ℝ)) 7 (123978722661/125000000000 : ℝ) (247957445323/250000000000 : ℝ) (123978722661/125000000000 : ℝ) (247957445323/250000000000 : ℝ) (123978722661/125000000000 : ℝ) (247957445323/250000000000 : ℝ) (123978722661/125000000000 : ℝ) (247957445323/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2155/16384 : ℝ))) (179855309123/1000000000000 : ℝ) (179855309129/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2155/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (179855309123/1000000000000 : ℝ) (179855309129/1000000000000 : ℝ) (589927654561/1000000000000 : ℝ) (117985530913/200000000000 : ℝ) (106023378649/250000000000 : ℝ) (106023378651/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2155/16384 : ℝ))) 1 (589927654561/1000000000000 : ℝ) (117985530913/200000000000 : ℝ) (106023378649/250000000000 : ℝ) (106023378651/250000000000 : ℝ) (253505292289/500000000000 : ℝ) (101402116917/200000000000 : ℝ) (100036891671/200000000000 : ℝ) (250092229181/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2155/16384 : ℝ))) 2 (253505292289/500000000000 : ℝ) (101402116917/200000000000 : ℝ) (100036891671/200000000000 : ℝ) (250092229181/500000000000 : ℝ) (251798760733/500000000000 : ℝ) (251798760737/500000000000 : ℝ) (10071719111/20000000000 : ℝ) (251792977779/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2155/16384 : ℝ))) 3 (251798760733/500000000000 : ℝ) (251798760737/500000000000 : ℝ) (10071719111/20000000000 : ℝ) (251792977779/500000000000 : ℝ) (125897934627/250000000000 : ℝ) (125897934629/250000000000 : ℝ) (251795869237/500000000000 : ℝ) (503591738483/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2155/16384 : ℝ))) 4 (125897934627/250000000000 : ℝ) (125897934629/250000000000 : ℝ) (251795869237/500000000000 : ℝ) (503591738483/1000000000000 : ℝ) (503591738491/1000000000000 : ℝ) (1007183477/2000000000 : ℝ) (50359173849/100000000000 : ℝ) (1007183477/2000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2155/16384 : ℝ))) 5 (503591738491/1000000000000 : ℝ) (1007183477/2000000000 : ℝ) (50359173849/100000000000 : ℝ) (1007183477/2000000000 : ℝ) (50359173849/100000000000 : ℝ) (1007183477/2000000000 : ℝ) (50359173849/100000000000 : ℝ) (1007183477/2000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2155/16384 : ℝ))) 6 (50359173849/100000000000 : ℝ) (1007183477/2000000000 : ℝ) (50359173849/100000000000 : ℝ) (1007183477/2000000000 : ℝ) (50359173849/100000000000 : ℝ) (1007183477/2000000000 : ℝ) (50359173849/100000000000 : ℝ) (1007183477/2000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2155/16384 : ℝ))) 7 (50359173849/100000000000 : ℝ) (1007183477/2000000000 : ℝ) (50359173849/100000000000 : ℝ) (1007183477/2000000000 : ℝ) (50359173849/100000000000 : ℝ) (1007183477/2000000000 : ℝ) (50359173849/100000000000 : ℝ) (1007183477/2000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2155/16384 : ℝ)) hmem 8 (123978722661/125000000000 : ℝ) (247957445323/250000000000 : ℝ) (123978722661/125000000000 : ℝ) (247957445323/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2155/16384 : ℝ))) hcmem 8 (50359173849/100000000000 : ℝ) (1007183477/2000000000 : ℝ) (50359173849/100000000000 : ℝ) (1007183477/2000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2155/16384 : ℝ)) (123978722661/125000000000 : ℝ) (247957445323/250000000000 : ℝ) (50359173849/100000000000 : ℝ) (1007183477/2000000000 : ℝ) (797556262117/1000000000000 : ℝ) (797556262137/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1590_exp_lower
  have heNumeric : (205492292903/100000000000 : ℝ)/4 ≤ Real.exp (-5328448143971/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205492292903/100000000000 : ℝ)/4 ≤ Real.exp ((4309/32768 : ℝ)-(797556262137/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4309/32768 : ℝ) (2155/16384 : ℝ) (797556262137/1000000000000 : ℝ) (205492292903/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1591; no trusted numerical premise.
theorem cover8_leaf1591_exp_radius : (124743308300267759/125000000000000000 : ℝ) ≤ Real.exp ((-4311/262144 : ℝ)/8) ∧ Real.exp ((-4311/262144 : ℝ)/8) ≤ (997946466402142073/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4311/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1591_exp_lower : (460057357904474381/500000000000000000 : ℝ) ≤ Real.exp ((-2664221619701/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664221619701/4000000000000 : ℝ)/8) ≤ (920114715808948763/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664221619701/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1591_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513731047211/250000000000 : ℝ) ≤ 4*Real.exp (2155/16384 : ℝ)*Real.exp (-mu (radius 8 (4311/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (513731047211/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4311/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1591_exp_radius
  have hrNumeric : (192126821/195312500 : ℝ) ≤ Real.exp (-4311/262144 : ℝ) ∧ Real.exp (-4311/262144 : ℝ) ≤ (983689323521/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (192126821/195312500 : ℝ) ≤ (radius 8 (4311/32768 : ℝ)) ∧ (radius 8 (4311/32768 : ℝ)) ≤ (983689323521/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4311/32768 : ℝ)) (192126821/195312500 : ℝ) (983689323521/1000000000000 : ℝ) (179875831591/1000000000000 : ℝ) (89937915799/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4311/32768 : ℝ)) (192126821/195312500 : ℝ) (983689323521/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4311/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (192126821/195312500 : ℝ) (983689323521/1000000000000 : ℝ) (387439321/390625000 : ℝ) (991844661761/1000000000000 : ℝ) (247952783247/250000000000 : ℝ) (99181113299/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4311/32768 : ℝ)) 1 (387439321/390625000 : ℝ) (991844661761/1000000000000 : ℝ) (247952783247/250000000000 : ℝ) (99181113299/100000000000 : ℝ) (495913948687/500000000000 : ℝ) (30994621793/31250000000 : ℝ) (61989243577/62500000000 : ℝ) (495913948617/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4311/32768 : ℝ)) 2 (495913948687/500000000000 : ℝ) (30994621793/31250000000 : ℝ) (61989243577/62500000000 : ℝ) (495913948617/500000000000 : ℝ) (991827897303/1000000000000 : ℝ) (198365579461/200000000000 : ℝ) (495913948651/500000000000 : ℝ) (198365579461/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4311/32768 : ℝ)) 3 (991827897303/1000000000000 : ℝ) (198365579461/200000000000 : ℝ) (495913948651/500000000000 : ℝ) (198365579461/200000000000 : ℝ) (495913948651/500000000000 : ℝ) (198365579461/200000000000 : ℝ) (495913948651/500000000000 : ℝ) (198365579461/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4311/32768 : ℝ)) 4 (495913948651/500000000000 : ℝ) (198365579461/200000000000 : ℝ) (495913948651/500000000000 : ℝ) (198365579461/200000000000 : ℝ) (495913948651/500000000000 : ℝ) (198365579461/200000000000 : ℝ) (495913948651/500000000000 : ℝ) (198365579461/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4311/32768 : ℝ)) 5 (495913948651/500000000000 : ℝ) (198365579461/200000000000 : ℝ) (495913948651/500000000000 : ℝ) (198365579461/200000000000 : ℝ) (495913948651/500000000000 : ℝ) (198365579461/200000000000 : ℝ) (495913948651/500000000000 : ℝ) (198365579461/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4311/32768 : ℝ)) 6 (495913948651/500000000000 : ℝ) (198365579461/200000000000 : ℝ) (495913948651/500000000000 : ℝ) (198365579461/200000000000 : ℝ) (495913948651/500000000000 : ℝ) (198365579461/200000000000 : ℝ) (495913948651/500000000000 : ℝ) (198365579461/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4311/32768 : ℝ)) 7 (495913948651/500000000000 : ℝ) (198365579461/200000000000 : ℝ) (495913948651/500000000000 : ℝ) (198365579461/200000000000 : ℝ) (495913948651/500000000000 : ℝ) (198365579461/200000000000 : ℝ) (495913948651/500000000000 : ℝ) (198365579461/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4311/32768 : ℝ))) (179875831591/1000000000000 : ℝ) (89937915799/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4311/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (179875831591/1000000000000 : ℝ) (89937915799/500000000000 : ℝ) (117987583159/200000000000 : ℝ) (589937915799/1000000000000 : ℝ) (424117709593/1000000000000 : ℝ) (212058854801/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4311/32768 : ℝ))) 1 (117987583159/200000000000 : ℝ) (589937915799/1000000000000 : ℝ) (424117709593/1000000000000 : ℝ) (212058854801/500000000000 : ℝ) (253513906347/500000000000 : ℝ) (507027812701/1000000000000 : ℝ) (500203076409/1000000000000 : ℝ) (500203076417/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4311/32768 : ℝ))) 2 (253513906347/500000000000 : ℝ) (507027812701/1000000000000 : ℝ) (500203076409/1000000000000 : ℝ) (500203076417/1000000000000 : ℝ) (503615444551/1000000000000 : ℝ) (503615444559/1000000000000 : ℝ) (125900970939/250000000000 : ℝ) (125900970941/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4311/32768 : ℝ))) 3 (503615444551/1000000000000 : ℝ) (503615444559/1000000000000 : ℝ) (125900970939/250000000000 : ℝ) (125900970941/250000000000 : ℝ) (503609664153/1000000000000 : ℝ) (251804832081/500000000000 : ℝ) (12590241603/25000000000 : ℝ) (503609664129/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4311/32768 : ℝ))) 4 (503609664153/1000000000000 : ℝ) (251804832081/500000000000 : ℝ) (12590241603/25000000000 : ℝ) (503609664129/1000000000000 : ℝ) (62951208017/125000000000 : ℝ) (251804832073/500000000000 : ℝ) (62951208017/125000000000 : ℝ) (251804832073/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4311/32768 : ℝ))) 5 (62951208017/125000000000 : ℝ) (251804832073/500000000000 : ℝ) (62951208017/125000000000 : ℝ) (251804832073/500000000000 : ℝ) (62951208017/125000000000 : ℝ) (251804832073/500000000000 : ℝ) (62951208017/125000000000 : ℝ) (251804832073/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4311/32768 : ℝ))) 6 (62951208017/125000000000 : ℝ) (251804832073/500000000000 : ℝ) (62951208017/125000000000 : ℝ) (251804832073/500000000000 : ℝ) (62951208017/125000000000 : ℝ) (251804832073/500000000000 : ℝ) (62951208017/125000000000 : ℝ) (251804832073/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4311/32768 : ℝ))) 7 (62951208017/125000000000 : ℝ) (251804832073/500000000000 : ℝ) (62951208017/125000000000 : ℝ) (251804832073/500000000000 : ℝ) (62951208017/125000000000 : ℝ) (251804832073/500000000000 : ℝ) (62951208017/125000000000 : ℝ) (251804832073/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4311/32768 : ℝ)) hmem 8 (495913948651/500000000000 : ℝ) (198365579461/200000000000 : ℝ) (495913948651/500000000000 : ℝ) (198365579461/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4311/32768 : ℝ))) hcmem 8 (62951208017/125000000000 : ℝ) (251804832073/500000000000 : ℝ) (62951208017/125000000000 : ℝ) (251804832073/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4311/32768 : ℝ)) (495913948651/500000000000 : ℝ) (198365579461/200000000000 : ℝ) (62951208017/125000000000 : ℝ) (251804832073/500000000000 : ℝ) (6380689333/8000000000 : ℝ) (199396541661/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1591_exp_lower
  have heNumeric : (513731047211/250000000000 : ℝ)/4 ≤ Real.exp (-2664221619701/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513731047211/250000000000 : ℝ)/4 ≤ Real.exp ((2155/16384 : ℝ)-(199396541661/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2155/16384 : ℝ) (4311/32768 : ℝ) (199396541661/250000000000 : ℝ) (513731047211/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1592; no trusted numerical premise.
theorem cover8_leaf1592_exp_radius : (997945990544298447/1000000000000000000 : ℝ) ≤ Real.exp ((-539/32768 : ℝ)/8) ∧ Real.exp ((-539/32768 : ℝ)/8) ≤ (62371624409018653/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-539/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1592_exp_lower : (2875358708939279/3125000000000000 : ℝ) ≤ Real.exp ((-5328438297297/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328438297297/8000000000000 : ℝ)/8) ≤ (920114786860569281/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328438297297/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1592_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054925458301/1000000000000 : ℝ) ≤ 4*Real.exp (4311/32768 : ℝ)*Real.exp (-mu (radius 8 (539/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (2054925458301/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (539/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1592_exp_radius
  have hrNumeric : (19673711421/20000000000 : ℝ) ≤ Real.exp (-539/32768 : ℝ) ∧ Real.exp (-539/32768 : ℝ) ≤ (983685571051/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (19673711421/20000000000 : ℝ) ≤ (radius 8 (539/4096 : ℝ)) ∧ (radius 8 (539/4096 : ℝ)) ≤ (983685571051/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (539/4096 : ℝ)) (19673711421/20000000000 : ℝ) (983685571051/1000000000000 : ℝ) (44974087891/250000000000 : ℝ) (17989635157/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (539/4096 : ℝ)) (19673711421/20000000000 : ℝ) (983685571051/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (539/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (19673711421/20000000000 : ℝ) (983685571051/1000000000000 : ℝ) (39673711421/40000000000 : ℝ) (495921392763/500000000000 : ℝ) (49590462063/50000000000 : ℝ) (495904620631/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (539/4096 : ℝ)) 1 (39673711421/40000000000 : ℝ) (495921392763/500000000000 : ℝ) (49590462063/50000000000 : ℝ) (495904620631/500000000000 : ℝ) (61989125837/62500000000 : ℝ) (495913006697/500000000000 : ℝ) (3967304053/4000000000 : ℝ) (991826013253/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (539/4096 : ℝ)) 2 (61989125837/62500000000 : ℝ) (495913006697/500000000000 : ℝ) (3967304053/4000000000 : ℝ) (991826013253/1000000000000 : ℝ) (991826013321/1000000000000 : ℝ) (247956503331/250000000000 : ℝ) (24795650333/25000000000 : ℝ) (247956503331/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (539/4096 : ℝ)) 3 (991826013321/1000000000000 : ℝ) (247956503331/250000000000 : ℝ) (24795650333/25000000000 : ℝ) (247956503331/250000000000 : ℝ) (24795650333/25000000000 : ℝ) (247956503331/250000000000 : ℝ) (24795650333/25000000000 : ℝ) (247956503331/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (539/4096 : ℝ)) 4 (24795650333/25000000000 : ℝ) (247956503331/250000000000 : ℝ) (24795650333/25000000000 : ℝ) (247956503331/250000000000 : ℝ) (24795650333/25000000000 : ℝ) (247956503331/250000000000 : ℝ) (24795650333/25000000000 : ℝ) (247956503331/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (539/4096 : ℝ)) 5 (24795650333/25000000000 : ℝ) (247956503331/250000000000 : ℝ) (24795650333/25000000000 : ℝ) (247956503331/250000000000 : ℝ) (24795650333/25000000000 : ℝ) (247956503331/250000000000 : ℝ) (24795650333/25000000000 : ℝ) (247956503331/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (539/4096 : ℝ)) 6 (24795650333/25000000000 : ℝ) (247956503331/250000000000 : ℝ) (24795650333/25000000000 : ℝ) (247956503331/250000000000 : ℝ) (24795650333/25000000000 : ℝ) (247956503331/250000000000 : ℝ) (24795650333/25000000000 : ℝ) (247956503331/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (539/4096 : ℝ)) 7 (24795650333/25000000000 : ℝ) (247956503331/250000000000 : ℝ) (24795650333/25000000000 : ℝ) (247956503331/250000000000 : ℝ) (24795650333/25000000000 : ℝ) (247956503331/250000000000 : ℝ) (24795650333/25000000000 : ℝ) (247956503331/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (539/4096 : ℝ))) (44974087891/250000000000 : ℝ) (17989635157/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (539/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44974087891/250000000000 : ℝ) (17989635157/100000000000 : ℝ) (294974087891/500000000000 : ℝ) (117989635157/200000000000 : ℝ) (424141900269/1000000000000 : ℝ) (424141900277/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (539/4096 : ℝ))) 1 (294974087891/500000000000 : ℝ) (117989635157/200000000000 : ℝ) (424141900269/1000000000000 : ℝ) (424141900277/1000000000000 : ℝ) (20281801521/40000000000 : ℝ) (507045038031/1000000000000 : ℝ) (500221691189/1000000000000 : ℝ) (125055422799/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (539/4096 : ℝ))) 2 (20281801521/40000000000 : ℝ) (507045038031/1000000000000 : ℝ) (500221691189/1000000000000 : ℝ) (125055422799/250000000000 : ℝ) (503633364607/1000000000000 : ℝ) (251816682307/500000000000 : ℝ) (503621808929/1000000000000 : ℝ) (503621808937/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (539/4096 : ℝ))) 3 (503633364607/1000000000000 : ℝ) (251816682307/500000000000 : ℝ) (503621808929/1000000000000 : ℝ) (503621808937/1000000000000 : ℝ) (31476724173/62500000000 : ℝ) (62953448347/125000000000 : ℝ) (251813793367/500000000000 : ℝ) (503627586743/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (539/4096 : ℝ))) 4 (31476724173/62500000000 : ℝ) (62953448347/125000000000 : ℝ) (251813793367/500000000000 : ℝ) (503627586743/1000000000000 : ℝ) (503627586751/1000000000000 : ℝ) (12590689669/25000000000 : ℝ) (2014510347/4000000000 : ℝ) (12590689669/25000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (539/4096 : ℝ))) 5 (503627586751/1000000000000 : ℝ) (12590689669/25000000000 : ℝ) (2014510347/4000000000 : ℝ) (12590689669/25000000000 : ℝ) (2014510347/4000000000 : ℝ) (12590689669/25000000000 : ℝ) (2014510347/4000000000 : ℝ) (12590689669/25000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (539/4096 : ℝ))) 6 (2014510347/4000000000 : ℝ) (12590689669/25000000000 : ℝ) (2014510347/4000000000 : ℝ) (12590689669/25000000000 : ℝ) (2014510347/4000000000 : ℝ) (12590689669/25000000000 : ℝ) (2014510347/4000000000 : ℝ) (12590689669/25000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (539/4096 : ℝ))) 7 (2014510347/4000000000 : ℝ) (12590689669/25000000000 : ℝ) (2014510347/4000000000 : ℝ) (12590689669/25000000000 : ℝ) (2014510347/4000000000 : ℝ) (12590689669/25000000000 : ℝ) (2014510347/4000000000 : ℝ) (12590689669/25000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (539/4096 : ℝ)) hmem 8 (24795650333/25000000000 : ℝ) (247956503331/250000000000 : ℝ) (24795650333/25000000000 : ℝ) (247956503331/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (539/4096 : ℝ))) hcmem 8 (2014510347/4000000000 : ℝ) (12590689669/25000000000 : ℝ) (2014510347/4000000000 : ℝ) (12590689669/25000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (539/4096 : ℝ)) (24795650333/25000000000 : ℝ) (247956503331/250000000000 : ℝ) (2014510347/4000000000 : ℝ) (12590689669/25000000000 : ℝ) (797616066439/1000000000000 : ℝ) (797616066459/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1592_exp_lower
  have heNumeric : (2054925458301/1000000000000 : ℝ)/4 ≤ Real.exp (-5328438297297/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054925458301/1000000000000 : ℝ)/4 ≤ Real.exp ((4311/32768 : ℝ)-(797616066459/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4311/32768 : ℝ) (539/4096 : ℝ) (797616066459/1000000000000 : ℝ) (2054925458301/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1593; no trusted numerical premise.
theorem cover8_leaf1593_exp_radius : (997945514686681729/1000000000000000000 : ℝ) ≤ Real.exp ((-4313/262144 : ℝ)/8) ∧ Real.exp ((-4313/262144 : ℝ)/8) ≤ (99794551468668173/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4313/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1593_exp_lower : (230028714613190691/250000000000000000 : ℝ) ≤ Real.exp ((-666054164699/1000000000000 : ℝ)/8) ∧ Real.exp ((-666054164699/1000000000000 : ℝ)/8) ≤ (184022971690552553/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666054164699/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1593_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054926737417/1000000000000 : ℝ) ≤ 4*Real.exp (539/4096 : ℝ)*Real.exp (-mu (radius 8 (4313/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054926737417/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4313/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1593_exp_radius
  have hrNumeric : (196736363719/200000000000 : ℝ) ≤ Real.exp (-4313/262144 : ℝ) ∧ Real.exp (-4313/262144 : ℝ) ≤ (245920454649/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196736363719/200000000000 : ℝ) ≤ (radius 8 (4313/32768 : ℝ)) ∧ (radius 8 (4313/32768 : ℝ)) ≤ (245920454649/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4313/32768 : ℝ)) (196736363719/200000000000 : ℝ) (245920454649/250000000000 : ℝ) (35983373807/200000000000 : ℝ) (89958434521/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4313/32768 : ℝ)) (196736363719/200000000000 : ℝ) (245920454649/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4313/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196736363719/200000000000 : ℝ) (245920454649/250000000000 : ℝ) (991840909297/1000000000000 : ℝ) (495920454649/500000000000 : ℝ) (30993979673/31250000000 : ℝ) (495903674769/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4313/32768 : ℝ)) 1 (991840909297/1000000000000 : ℝ) (495920454649/500000000000 : ℝ) (30993979673/31250000000 : ℝ) (495903674769/500000000000 : ℝ) (123978016177/125000000000 : ℝ) (495912064709/500000000000 : ℝ) (495912064637/500000000000 : ℝ) (991824129277/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4313/32768 : ℝ)) 2 (123978016177/125000000000 : ℝ) (495912064709/500000000000 : ℝ) (495912064637/500000000000 : ℝ) (991824129277/1000000000000 : ℝ) (198364825869/200000000000 : ℝ) (247956032337/250000000000 : ℝ) (15497252021/15625000000 : ℝ) (247956032337/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4313/32768 : ℝ)) 3 (198364825869/200000000000 : ℝ) (247956032337/250000000000 : ℝ) (15497252021/15625000000 : ℝ) (247956032337/250000000000 : ℝ) (15497252021/15625000000 : ℝ) (247956032337/250000000000 : ℝ) (15497252021/15625000000 : ℝ) (247956032337/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4313/32768 : ℝ)) 4 (15497252021/15625000000 : ℝ) (247956032337/250000000000 : ℝ) (15497252021/15625000000 : ℝ) (247956032337/250000000000 : ℝ) (15497252021/15625000000 : ℝ) (247956032337/250000000000 : ℝ) (15497252021/15625000000 : ℝ) (247956032337/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4313/32768 : ℝ)) 5 (15497252021/15625000000 : ℝ) (247956032337/250000000000 : ℝ) (15497252021/15625000000 : ℝ) (247956032337/250000000000 : ℝ) (15497252021/15625000000 : ℝ) (247956032337/250000000000 : ℝ) (15497252021/15625000000 : ℝ) (247956032337/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4313/32768 : ℝ)) 6 (15497252021/15625000000 : ℝ) (247956032337/250000000000 : ℝ) (15497252021/15625000000 : ℝ) (247956032337/250000000000 : ℝ) (15497252021/15625000000 : ℝ) (247956032337/250000000000 : ℝ) (15497252021/15625000000 : ℝ) (247956032337/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4313/32768 : ℝ)) 7 (15497252021/15625000000 : ℝ) (247956032337/250000000000 : ℝ) (15497252021/15625000000 : ℝ) (247956032337/250000000000 : ℝ) (15497252021/15625000000 : ℝ) (247956032337/250000000000 : ℝ) (15497252021/15625000000 : ℝ) (247956032337/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4313/32768 : ℝ))) (35983373807/200000000000 : ℝ) (89958434521/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4313/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35983373807/200000000000 : ℝ) (89958434521/500000000000 : ℝ) (589958434517/1000000000000 : ℝ) (589958434521/1000000000000 : ℝ) (84833217323/200000000000 : ℝ) (3393328693/8000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4313/32768 : ℝ))) 1 (589958434517/1000000000000 : ℝ) (589958434521/1000000000000 : ℝ) (84833217323/200000000000 : ℝ) (3393328693/8000000000 : ℝ) (253531130283/500000000000 : ℝ) (507062260573/1000000000000 : ℝ) (500240302689/1000000000000 : ℝ) (500240302697/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4313/32768 : ℝ))) 2 (253531130283/500000000000 : ℝ) (507062260573/1000000000000 : ℝ) (500240302689/1000000000000 : ℝ) (500240302697/1000000000000 : ℝ) (503651281627/1000000000000 : ℝ) (100730256327/200000000000 : ℝ) (100727946213/200000000000 : ℝ) (503639731073/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4313/32768 : ℝ))) 3 (503651281627/1000000000000 : ℝ) (100730256327/200000000000 : ℝ) (100727946213/200000000000 : ℝ) (503639731073/1000000000000 : ℝ) (251822753173/500000000000 : ℝ) (251822753177/500000000000 : ℝ) (62955688289/125000000000 : ℝ) (503645506321/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4313/32768 : ℝ))) 4 (251822753173/500000000000 : ℝ) (251822753177/500000000000 : ℝ) (62955688289/125000000000 : ℝ) (503645506321/1000000000000 : ℝ) (503645506329/1000000000000 : ℝ) (251822753169/500000000000 : ℝ) (62955688291/125000000000 : ℝ) (251822753169/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4313/32768 : ℝ))) 5 (503645506329/1000000000000 : ℝ) (251822753169/500000000000 : ℝ) (62955688291/125000000000 : ℝ) (251822753169/500000000000 : ℝ) (62955688291/125000000000 : ℝ) (251822753169/500000000000 : ℝ) (62955688291/125000000000 : ℝ) (251822753169/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4313/32768 : ℝ))) 6 (62955688291/125000000000 : ℝ) (251822753169/500000000000 : ℝ) (62955688291/125000000000 : ℝ) (251822753169/500000000000 : ℝ) (62955688291/125000000000 : ℝ) (251822753169/500000000000 : ℝ) (62955688291/125000000000 : ℝ) (251822753169/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4313/32768 : ℝ))) 7 (62955688291/125000000000 : ℝ) (251822753169/500000000000 : ℝ) (62955688291/125000000000 : ℝ) (251822753169/500000000000 : ℝ) (62955688291/125000000000 : ℝ) (251822753169/500000000000 : ℝ) (62955688291/125000000000 : ℝ) (251822753169/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4313/32768 : ℝ)) hmem 8 (15497252021/15625000000 : ℝ) (247956032337/250000000000 : ℝ) (15497252021/15625000000 : ℝ) (247956032337/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4313/32768 : ℝ))) hcmem 8 (62955688291/125000000000 : ℝ) (251822753169/500000000000 : ℝ) (62955688291/125000000000 : ℝ) (251822753169/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4313/32768 : ℝ)) (15497252021/15625000000 : ℝ) (247956032337/250000000000 : ℝ) (62955688291/125000000000 : ℝ) (251822753169/500000000000 : ℝ) (398822980777/500000000000 : ℝ) (398822980787/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1593_exp_lower
  have heNumeric : (2054926737417/1000000000000 : ℝ)/4 ≤ Real.exp (-666054164699/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054926737417/1000000000000 : ℝ)/4 ≤ Real.exp ((539/4096 : ℝ)-(398822980787/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (539/4096 : ℝ) (4313/32768 : ℝ) (398822980787/500000000000 : ℝ) (2054926737417/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1594; no trusted numerical premise.
theorem cover8_leaf1594_exp_radius : (498972519414645959/500000000000000000 : ℝ) ≤ Real.exp ((-2157/131072 : ℝ)/8) ∧ Real.exp ((-2157/131072 : ℝ)/8) ≤ (997945038829291919/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2157/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1594_exp_lower : (184022986116553799/200000000000000000 : ℝ) ≤ Real.exp ((-5328428300479/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328428300479/8000000000000 : ℝ)/8) ≤ (230028732645692249/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328428300479/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1594_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027464013071/500000000000 : ℝ) ≤ 4*Real.exp (4313/32768 : ℝ)*Real.exp (-mu (radius 8 (2157/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (1027464013071/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2157/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1594_exp_radius
  have hrNumeric : (983678066153/1000000000000 : ℝ) ≤ Real.exp (-2157/131072 : ℝ) ∧ Real.exp (-2157/131072 : ℝ) ≤ (491839033077/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983678066153/1000000000000 : ℝ) ≤ (radius 8 (2157/16384 : ℝ)) ∧ (radius 8 (2157/16384 : ℝ)) ≤ (491839033077/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2157/16384 : ℝ)) (983678066153/1000000000000 : ℝ) (491839033077/500000000000 : ℝ) (89968692009/500000000000 : ℝ) (7197495361/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2157/16384 : ℝ)) (983678066153/1000000000000 : ℝ) (491839033077/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2157/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983678066153/1000000000000 : ℝ) (491839033077/500000000000 : ℝ) (247959758269/250000000000 : ℝ) (991839033077/1000000000000 : ℝ) (198361091563/200000000000 : ℝ) (991805457817/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2157/16384 : ℝ)) 1 (247959758269/250000000000 : ℝ) (991839033077/1000000000000 : ℝ) (198361091563/200000000000 : ℝ) (991805457817/1000000000000 : ℝ) (198364449089/200000000000 : ℝ) (991822245447/1000000000000 : ℝ) (991822245303/1000000000000 : ℝ) (198364449061/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2157/16384 : ℝ)) 2 (198364449089/200000000000 : ℝ) (991822245447/1000000000000 : ℝ) (991822245303/1000000000000 : ℝ) (198364449061/200000000000 : ℝ) (495911122687/500000000000 : ℝ) (1937152823/1953125000 : ℝ) (991822245373/1000000000000 : ℝ) (1937152823/1953125000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2157/16384 : ℝ)) 3 (495911122687/500000000000 : ℝ) (1937152823/1953125000 : ℝ) (991822245373/1000000000000 : ℝ) (1937152823/1953125000 : ℝ) (991822245373/1000000000000 : ℝ) (1937152823/1953125000 : ℝ) (991822245373/1000000000000 : ℝ) (1937152823/1953125000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2157/16384 : ℝ)) 4 (991822245373/1000000000000 : ℝ) (1937152823/1953125000 : ℝ) (991822245373/1000000000000 : ℝ) (1937152823/1953125000 : ℝ) (991822245373/1000000000000 : ℝ) (1937152823/1953125000 : ℝ) (991822245373/1000000000000 : ℝ) (1937152823/1953125000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2157/16384 : ℝ)) 5 (991822245373/1000000000000 : ℝ) (1937152823/1953125000 : ℝ) (991822245373/1000000000000 : ℝ) (1937152823/1953125000 : ℝ) (991822245373/1000000000000 : ℝ) (1937152823/1953125000 : ℝ) (991822245373/1000000000000 : ℝ) (1937152823/1953125000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2157/16384 : ℝ)) 6 (991822245373/1000000000000 : ℝ) (1937152823/1953125000 : ℝ) (991822245373/1000000000000 : ℝ) (1937152823/1953125000 : ℝ) (991822245373/1000000000000 : ℝ) (1937152823/1953125000 : ℝ) (991822245373/1000000000000 : ℝ) (1937152823/1953125000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2157/16384 : ℝ)) 7 (991822245373/1000000000000 : ℝ) (1937152823/1953125000 : ℝ) (991822245373/1000000000000 : ℝ) (1937152823/1953125000 : ℝ) (991822245373/1000000000000 : ℝ) (1937152823/1953125000 : ℝ) (991822245373/1000000000000 : ℝ) (1937152823/1953125000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2157/16384 : ℝ))) (89968692009/500000000000 : ℝ) (7197495361/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2157/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89968692009/500000000000 : ℝ) (7197495361/40000000000 : ℝ) (589968692009/1000000000000 : ℝ) (589968692013/1000000000000 : ℝ) (8483805373/20000000000 : ℝ) (21209513433/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2157/16384 : ℝ))) 1 (589968692009/1000000000000 : ℝ) (589968692013/1000000000000 : ℝ) (8483805373/20000000000 : ℝ) (21209513433/50000000000 : ℝ) (507079480329/1000000000000 : ℝ) (507079480337/1000000000000 : ℝ) (500258910923/1000000000000 : ℝ) (125064727733/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2157/16384 : ℝ))) 2 (507079480329/1000000000000 : ℝ) (507079480337/1000000000000 : ℝ) (500258910923/1000000000000 : ℝ) (125064727733/250000000000 : ℝ) (251834597813/500000000000 : ℝ) (100733839127/200000000000 : ℝ) (20146306007/40000000000 : ℝ) (100731530037/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2157/16384 : ℝ))) 3 (251834597813/500000000000 : ℝ) (100733839127/200000000000 : ℝ) (20146306007/40000000000 : ℝ) (100731530037/200000000000 : ℝ) (5036634229/10000000000 : ℝ) (50366342291/100000000000 : ℝ) (503663422867/1000000000000 : ℝ) (503663422877/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2157/16384 : ℝ))) 4 (5036634229/10000000000 : ℝ) (50366342291/100000000000 : ℝ) (503663422867/1000000000000 : ℝ) (503663422877/1000000000000 : ℝ) (503663422883/1000000000000 : ℝ) (251831711447/500000000000 : ℝ) (503663422883/1000000000000 : ℝ) (251831711447/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2157/16384 : ℝ))) 5 (503663422883/1000000000000 : ℝ) (251831711447/500000000000 : ℝ) (503663422883/1000000000000 : ℝ) (251831711447/500000000000 : ℝ) (503663422883/1000000000000 : ℝ) (251831711447/500000000000 : ℝ) (503663422883/1000000000000 : ℝ) (251831711447/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2157/16384 : ℝ))) 6 (503663422883/1000000000000 : ℝ) (251831711447/500000000000 : ℝ) (503663422883/1000000000000 : ℝ) (251831711447/500000000000 : ℝ) (503663422883/1000000000000 : ℝ) (251831711447/500000000000 : ℝ) (503663422883/1000000000000 : ℝ) (251831711447/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2157/16384 : ℝ))) 7 (503663422883/1000000000000 : ℝ) (251831711447/500000000000 : ℝ) (503663422883/1000000000000 : ℝ) (251831711447/500000000000 : ℝ) (503663422883/1000000000000 : ℝ) (251831711447/500000000000 : ℝ) (503663422883/1000000000000 : ℝ) (251831711447/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2157/16384 : ℝ)) hmem 8 (991822245373/1000000000000 : ℝ) (1937152823/1953125000 : ℝ) (991822245373/1000000000000 : ℝ) (1937152823/1953125000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2157/16384 : ℝ))) hcmem 8 (503663422883/1000000000000 : ℝ) (251831711447/500000000000 : ℝ) (503663422883/1000000000000 : ℝ) (251831711447/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2157/16384 : ℝ)) (991822245373/1000000000000 : ℝ) (1937152823/1953125000 : ℝ) (503663422883/1000000000000 : ℝ) (251831711447/500000000000 : ℝ) (99709481499/125000000000 : ℝ) (797675852013/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1594_exp_lower
  have heNumeric : (1027464013071/500000000000 : ℝ)/4 ≤ Real.exp (-5328428300479/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027464013071/500000000000 : ℝ)/4 ≤ Real.exp ((4313/32768 : ℝ)-(797675852013/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4313/32768 : ℝ) (2157/16384 : ℝ) (797675852013/1000000000000 : ℝ) (1027464013071/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1595; no trusted numerical premise.
theorem cover8_leaf1595_exp_radius : (997944562972129013/1000000000000000000 : ℝ) ≤ Real.exp ((-4315/262144 : ℝ)/8) ∧ Real.exp ((-4315/262144 : ℝ)/8) ≤ (498972281486064507/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4315/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1595_exp_lower : (184023000650830709/200000000000000000 : ℝ) ≤ Real.exp ((-532842324571/800000000000 : ℝ)/8) ∧ Real.exp ((-532842324571/800000000000 : ℝ)/8) ≤ (460057501627076773/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-532842324571/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1595_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054929324541/1000000000000 : ℝ) ≤ 4*Real.exp (2157/16384 : ℝ)*Real.exp (-mu (radius 8 (4315/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054929324541/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4315/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1595_exp_radius
  have hrNumeric : (983674313727/1000000000000 : ℝ) ≤ Real.exp (-4315/262144 : ℝ) ∧ Real.exp (-4315/262144 : ℝ) ≤ (960619447/976562500 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983674313727/1000000000000 : ℝ) ≤ (radius 8 (4315/32768 : ℝ)) ∧ (radius 8 (4315/32768 : ℝ)) ≤ (960619447/976562500 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4315/32768 : ℝ)) (983674313727/1000000000000 : ℝ) (960619447/976562500 : ℝ) (179957896497/1000000000000 : ℝ) (179957896503/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4315/32768 : ℝ)) (983674313727/1000000000000 : ℝ) (960619447/976562500 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4315/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983674313727/1000000000000 : ℝ) (960619447/976562500 : ℝ) (991837156863/1000000000000 : ℝ) (1937181947/1953125000 : ℝ) (991803566099/1000000000000 : ℝ) (9918035661/10000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4315/32768 : ℝ)) 1 (991837156863/1000000000000 : ℝ) (1937181947/1953125000 : ℝ) (991803566099/1000000000000 : ℝ) (9918035661/10000000000 : ℝ) (991820361481/1000000000000 : ℝ) (495910180741/500000000000 : ℝ) (495910180669/500000000000 : ℝ) (49591018067/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4315/32768 : ℝ)) 2 (991820361481/1000000000000 : ℝ) (495910180741/500000000000 : ℝ) (495910180669/500000000000 : ℝ) (49591018067/50000000000 : ℝ) (991820361409/1000000000000 : ℝ) (991820361411/1000000000000 : ℝ) (991820361409/1000000000000 : ℝ) (991820361411/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4315/32768 : ℝ)) 3 (991820361409/1000000000000 : ℝ) (991820361411/1000000000000 : ℝ) (991820361409/1000000000000 : ℝ) (991820361411/1000000000000 : ℝ) (991820361409/1000000000000 : ℝ) (991820361411/1000000000000 : ℝ) (991820361409/1000000000000 : ℝ) (991820361411/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4315/32768 : ℝ)) 4 (991820361409/1000000000000 : ℝ) (991820361411/1000000000000 : ℝ) (991820361409/1000000000000 : ℝ) (991820361411/1000000000000 : ℝ) (991820361409/1000000000000 : ℝ) (991820361411/1000000000000 : ℝ) (991820361409/1000000000000 : ℝ) (991820361411/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4315/32768 : ℝ)) 5 (991820361409/1000000000000 : ℝ) (991820361411/1000000000000 : ℝ) (991820361409/1000000000000 : ℝ) (991820361411/1000000000000 : ℝ) (991820361409/1000000000000 : ℝ) (991820361411/1000000000000 : ℝ) (991820361409/1000000000000 : ℝ) (991820361411/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4315/32768 : ℝ)) 6 (991820361409/1000000000000 : ℝ) (991820361411/1000000000000 : ℝ) (991820361409/1000000000000 : ℝ) (991820361411/1000000000000 : ℝ) (991820361409/1000000000000 : ℝ) (991820361411/1000000000000 : ℝ) (991820361409/1000000000000 : ℝ) (991820361411/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4315/32768 : ℝ)) 7 (991820361409/1000000000000 : ℝ) (991820361411/1000000000000 : ℝ) (991820361409/1000000000000 : ℝ) (991820361411/1000000000000 : ℝ) (991820361409/1000000000000 : ℝ) (991820361411/1000000000000 : ℝ) (991820361409/1000000000000 : ℝ) (991820361411/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4315/32768 : ℝ))) (179957896497/1000000000000 : ℝ) (179957896503/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4315/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (179957896497/1000000000000 : ℝ) (179957896503/1000000000000 : ℝ) (73747368531/125000000000 : ℝ) (147494737063/250000000000 : ℝ) (84842889271/200000000000 : ℝ) (424214446363/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4315/32768 : ℝ))) 1 (73747368531/125000000000 : ℝ) (147494737063/250000000000 : ℝ) (84842889271/200000000000 : ℝ) (424214446363/1000000000000 : ℝ) (507096697301/1000000000000 : ℝ) (126774174327/250000000000 : ℝ) (500277515877/1000000000000 : ℝ) (125069378971/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4315/32768 : ℝ))) 2 (507096697301/1000000000000 : ℝ) (126774174327/250000000000 : ℝ) (500277515877/1000000000000 : ℝ) (125069378971/250000000000 : ℝ) (503687106589/1000000000000 : ℝ) (125921776649/250000000000 : ℝ) (503675566247/1000000000000 : ℝ) (100735113251/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4315/32768 : ℝ))) 3 (503687106589/1000000000000 : ℝ) (125921776649/250000000000 : ℝ) (503675566247/1000000000000 : ℝ) (100735113251/200000000000 : ℝ) (251840668209/500000000000 : ℝ) (251840668213/500000000000 : ℝ) (7870020881/15625000000 : ℝ) (503681336393/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4315/32768 : ℝ))) 4 (251840668209/500000000000 : ℝ) (251840668213/500000000000 : ℝ) (7870020881/15625000000 : ℝ) (503681336393/1000000000000 : ℝ) (503681336401/1000000000000 : ℝ) (50368133641/100000000000 : ℝ) (1259203341/2500000000 : ℝ) (50368133641/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4315/32768 : ℝ))) 5 (503681336401/1000000000000 : ℝ) (50368133641/100000000000 : ℝ) (1259203341/2500000000 : ℝ) (50368133641/100000000000 : ℝ) (1259203341/2500000000 : ℝ) (50368133641/100000000000 : ℝ) (1259203341/2500000000 : ℝ) (50368133641/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4315/32768 : ℝ))) 6 (1259203341/2500000000 : ℝ) (50368133641/100000000000 : ℝ) (1259203341/2500000000 : ℝ) (50368133641/100000000000 : ℝ) (1259203341/2500000000 : ℝ) (50368133641/100000000000 : ℝ) (1259203341/2500000000 : ℝ) (50368133641/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4315/32768 : ℝ))) 7 (1259203341/2500000000 : ℝ) (50368133641/100000000000 : ℝ) (1259203341/2500000000 : ℝ) (50368133641/100000000000 : ℝ) (1259203341/2500000000 : ℝ) (50368133641/100000000000 : ℝ) (1259203341/2500000000 : ℝ) (50368133641/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4315/32768 : ℝ)) hmem 8 (991820361409/1000000000000 : ℝ) (991820361411/1000000000000 : ℝ) (991820361409/1000000000000 : ℝ) (991820361411/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4315/32768 : ℝ))) hcmem 8 (1259203341/2500000000 : ℝ) (50368133641/100000000000 : ℝ) (1259203341/2500000000 : ℝ) (50368133641/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4315/32768 : ℝ)) (991820361409/1000000000000 : ℝ) (991820361411/1000000000000 : ℝ) (1259203341/2500000000 : ℝ) (50368133641/100000000000 : ℝ) (797705737727/1000000000000 : ℝ) (159541147549/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1595_exp_lower
  have heNumeric : (2054929324541/1000000000000 : ℝ)/4 ≤ Real.exp (-532842324571/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054929324541/1000000000000 : ℝ)/4 ≤ Real.exp ((2157/16384 : ℝ)-(159541147549/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2157/16384 : ℝ) (4315/32768 : ℝ) (159541147549/200000000000 : ℝ) (2054929324541/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1596; no trusted numerical premise.
theorem cover8_leaf1596_exp_radius : (498972043557596507/500000000000000000 : ℝ) ≤ Real.exp ((-1079/65536 : ℝ)/8) ∧ Real.exp ((-1079/65536 : ℝ)/8) ≤ (199588817423038603/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1079/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1596_exp_lower : (5750719227893069/6250000000000000 : ℝ) ≤ Real.exp ((-1065683630713/1600000000000 : ℝ)/8) ∧ Real.exp ((-1065683630713/1600000000000 : ℝ)/8) ≤ (920115076462891041/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1065683630713/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1596_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054930632541/1000000000000 : ℝ) ≤ 4*Real.exp (4315/32768 : ℝ)*Real.exp (-mu (radius 8 (1079/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (2054930632541/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1079/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1596_exp_radius
  have hrNumeric : (491835280657/500000000000 : ℝ) ≤ Real.exp (-1079/65536 : ℝ) ∧ Real.exp (-1079/65536 : ℝ) ≤ (196734112263/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491835280657/500000000000 : ℝ) ≤ (radius 8 (1079/8192 : ℝ)) ∧ (radius 8 (1079/8192 : ℝ)) ≤ (196734112263/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1079/8192 : ℝ)) (491835280657/500000000000 : ℝ) (196734112263/200000000000 : ℝ) (22497300811/125000000000 : ℝ) (35995681299/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1079/8192 : ℝ)) (491835280657/500000000000 : ℝ) (196734112263/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1079/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491835280657/500000000000 : ℝ) (196734112263/200000000000 : ℝ) (991835280657/1000000000000 : ℝ) (495917640329/500000000000 : ℝ) (198360334877/200000000000 : ℝ) (991801674387/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1079/8192 : ℝ)) 1 (991835280657/1000000000000 : ℝ) (495917640329/500000000000 : ℝ) (198360334877/200000000000 : ℝ) (991801674387/1000000000000 : ℝ) (991818477521/1000000000000 : ℝ) (991818477523/1000000000000 : ℝ) (495909238689/500000000000 : ℝ) (991818477381/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1079/8192 : ℝ)) 2 (991818477521/1000000000000 : ℝ) (991818477523/1000000000000 : ℝ) (495909238689/500000000000 : ℝ) (991818477381/1000000000000 : ℝ) (991818477449/1000000000000 : ℝ) (247954619363/250000000000 : ℝ) (991818477449/1000000000000 : ℝ) (247954619363/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1079/8192 : ℝ)) 3 (991818477449/1000000000000 : ℝ) (247954619363/250000000000 : ℝ) (991818477449/1000000000000 : ℝ) (247954619363/250000000000 : ℝ) (991818477449/1000000000000 : ℝ) (247954619363/250000000000 : ℝ) (991818477449/1000000000000 : ℝ) (247954619363/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1079/8192 : ℝ)) 4 (991818477449/1000000000000 : ℝ) (247954619363/250000000000 : ℝ) (991818477449/1000000000000 : ℝ) (247954619363/250000000000 : ℝ) (991818477449/1000000000000 : ℝ) (247954619363/250000000000 : ℝ) (991818477449/1000000000000 : ℝ) (247954619363/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1079/8192 : ℝ)) 5 (991818477449/1000000000000 : ℝ) (247954619363/250000000000 : ℝ) (991818477449/1000000000000 : ℝ) (247954619363/250000000000 : ℝ) (991818477449/1000000000000 : ℝ) (247954619363/250000000000 : ℝ) (991818477449/1000000000000 : ℝ) (247954619363/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1079/8192 : ℝ)) 6 (991818477449/1000000000000 : ℝ) (247954619363/250000000000 : ℝ) (991818477449/1000000000000 : ℝ) (247954619363/250000000000 : ℝ) (991818477449/1000000000000 : ℝ) (247954619363/250000000000 : ℝ) (991818477449/1000000000000 : ℝ) (247954619363/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1079/8192 : ℝ)) 7 (991818477449/1000000000000 : ℝ) (247954619363/250000000000 : ℝ) (991818477449/1000000000000 : ℝ) (247954619363/250000000000 : ℝ) (991818477449/1000000000000 : ℝ) (247954619363/250000000000 : ℝ) (991818477449/1000000000000 : ℝ) (247954619363/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1079/8192 : ℝ))) (22497300811/125000000000 : ℝ) (35995681299/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1079/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22497300811/125000000000 : ℝ) (35995681299/200000000000 : ℝ) (147497300811/250000000000 : ℝ) (36874325203/62500000000 : ℝ) (1696954479/4000000000 : ℝ) (424238619759/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1079/8192 : ℝ))) 1 (147497300811/250000000000 : ℝ) (36874325203/62500000000 : ℝ) (1696954479/4000000000 : ℝ) (424238619759/1000000000000 : ℝ) (507113911497/1000000000000 : ℝ) (31694619469/62500000000 : ℝ) (250148058783/500000000000 : ℝ) (250148058787/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1079/8192 : ℝ))) 2 (507113911497/1000000000000 : ℝ) (31694619469/62500000000 : ℝ) (250148058783/500000000000 : ℝ) (250148058787/500000000000 : ℝ) (503705014531/1000000000000 : ℝ) (503705014539/1000000000000 : ℝ) (3935105307/7812500000 : ℝ) (62961684913/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1079/8192 : ℝ))) 3 (503705014531/1000000000000 : ℝ) (503705014539/1000000000000 : ℝ) (3935105307/7812500000 : ℝ) (62961684913/125000000000 : ℝ) (503699246913/1000000000000 : ℝ) (251849623461/500000000000 : ℝ) (3148120293/6250000000 : ℝ) (503699246889/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1079/8192 : ℝ))) 4 (503699246913/1000000000000 : ℝ) (251849623461/500000000000 : ℝ) (3148120293/6250000000 : ℝ) (503699246889/1000000000000 : ℝ) (31481202931/62500000000 : ℝ) (251849623453/500000000000 : ℝ) (31481202931/62500000000 : ℝ) (251849623453/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1079/8192 : ℝ))) 5 (31481202931/62500000000 : ℝ) (251849623453/500000000000 : ℝ) (31481202931/62500000000 : ℝ) (251849623453/500000000000 : ℝ) (31481202931/62500000000 : ℝ) (251849623453/500000000000 : ℝ) (31481202931/62500000000 : ℝ) (251849623453/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1079/8192 : ℝ))) 6 (31481202931/62500000000 : ℝ) (251849623453/500000000000 : ℝ) (31481202931/62500000000 : ℝ) (251849623453/500000000000 : ℝ) (31481202931/62500000000 : ℝ) (251849623453/500000000000 : ℝ) (31481202931/62500000000 : ℝ) (251849623453/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1079/8192 : ℝ))) 7 (31481202931/62500000000 : ℝ) (251849623453/500000000000 : ℝ) (31481202931/62500000000 : ℝ) (251849623453/500000000000 : ℝ) (31481202931/62500000000 : ℝ) (251849623453/500000000000 : ℝ) (31481202931/62500000000 : ℝ) (251849623453/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1079/8192 : ℝ)) hmem 8 (991818477449/1000000000000 : ℝ) (247954619363/250000000000 : ℝ) (991818477449/1000000000000 : ℝ) (247954619363/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1079/8192 : ℝ))) hcmem 8 (31481202931/62500000000 : ℝ) (251849623453/500000000000 : ℝ) (31481202931/62500000000 : ℝ) (251849623453/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1079/8192 : ℝ)) (991818477449/1000000000000 : ℝ) (247954619363/250000000000 : ℝ) (31481202931/62500000000 : ℝ) (251849623453/500000000000 : ℝ) (398867809393/500000000000 : ℝ) (159547123761/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1596_exp_lower
  have heNumeric : (2054930632541/1000000000000 : ℝ)/4 ≤ Real.exp (-1065683630713/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054930632541/1000000000000 : ℝ)/4 ≤ Real.exp ((4315/32768 : ℝ)-(159547123761/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4315/32768 : ℝ) (1079/8192 : ℝ) (159547123761/200000000000 : ℝ) (2054930632541/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1597; no trusted numerical premise.
theorem cover8_leaf1597_exp_radius : (498971805629241961/500000000000000000 : ℝ) ≤ Real.exp ((-4317/262144 : ℝ)/8) ∧ Real.exp ((-4317/262144 : ℝ)/8) ≤ (997943611258483923/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4317/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1597_exp_lower : (5750719688819793/6250000000000000 : ℝ) ≤ Real.exp ((-1332103255973/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332103255973/2000000000000 : ℝ)/8) ≤ (920115150211166881/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332103255973/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1597_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027465975091/500000000000 : ℝ) ≤ 4*Real.exp (1079/8192 : ℝ)*Real.exp (-mu (radius 8 (4317/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (1027465975091/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4317/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1597_exp_radius
  have hrNumeric : (245916702229/250000000000 : ℝ) ≤ Real.exp (-4317/262144 : ℝ) ∧ Real.exp (-4317/262144 : ℝ) ≤ (983666808917/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245916702229/250000000000 : ℝ) ≤ (radius 8 (4317/32768 : ℝ)) ∧ (radius 8 (4317/32768 : ℝ)) ≤ (983666808917/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4317/32768 : ℝ)) (245916702229/250000000000 : ℝ) (983666808917/1000000000000 : ℝ) (89999456991/500000000000 : ℝ) (179998913989/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4317/32768 : ℝ)) (245916702229/250000000000 : ℝ) (983666808917/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4317/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245916702229/250000000000 : ℝ) (983666808917/1000000000000 : ℝ) (495916702229/500000000000 : ℝ) (991833404459/1000000000000 : ℝ) (39671991307/40000000000 : ℝ) (991799782677/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4317/32768 : ℝ)) 1 (495916702229/500000000000 : ℝ) (991833404459/1000000000000 : ℝ) (39671991307/40000000000 : ℝ) (991799782677/1000000000000 : ℝ) (495908296783/500000000000 : ℝ) (30994268549/31250000000 : ℝ) (61988537089/62500000000 : ℝ) (495908296713/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4317/32768 : ℝ)) 2 (495908296783/500000000000 : ℝ) (30994268549/31250000000 : ℝ) (61988537089/62500000000 : ℝ) (495908296713/500000000000 : ℝ) (198363318699/200000000000 : ℝ) (991816593497/1000000000000 : ℝ) (495908296747/500000000000 : ℝ) (991816593497/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4317/32768 : ℝ)) 3 (198363318699/200000000000 : ℝ) (991816593497/1000000000000 : ℝ) (495908296747/500000000000 : ℝ) (991816593497/1000000000000 : ℝ) (495908296747/500000000000 : ℝ) (991816593497/1000000000000 : ℝ) (495908296747/500000000000 : ℝ) (991816593497/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4317/32768 : ℝ)) 4 (495908296747/500000000000 : ℝ) (991816593497/1000000000000 : ℝ) (495908296747/500000000000 : ℝ) (991816593497/1000000000000 : ℝ) (495908296747/500000000000 : ℝ) (991816593497/1000000000000 : ℝ) (495908296747/500000000000 : ℝ) (991816593497/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4317/32768 : ℝ)) 5 (495908296747/500000000000 : ℝ) (991816593497/1000000000000 : ℝ) (495908296747/500000000000 : ℝ) (991816593497/1000000000000 : ℝ) (495908296747/500000000000 : ℝ) (991816593497/1000000000000 : ℝ) (495908296747/500000000000 : ℝ) (991816593497/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4317/32768 : ℝ)) 6 (495908296747/500000000000 : ℝ) (991816593497/1000000000000 : ℝ) (495908296747/500000000000 : ℝ) (991816593497/1000000000000 : ℝ) (495908296747/500000000000 : ℝ) (991816593497/1000000000000 : ℝ) (495908296747/500000000000 : ℝ) (991816593497/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4317/32768 : ℝ)) 7 (495908296747/500000000000 : ℝ) (991816593497/1000000000000 : ℝ) (495908296747/500000000000 : ℝ) (991816593497/1000000000000 : ℝ) (495908296747/500000000000 : ℝ) (991816593497/1000000000000 : ℝ) (495908296747/500000000000 : ℝ) (991816593497/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4317/32768 : ℝ))) (89999456991/500000000000 : ℝ) (179998913989/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4317/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89999456991/500000000000 : ℝ) (179998913989/1000000000000 : ℝ) (589999456991/1000000000000 : ℝ) (117999891399/200000000000 : ℝ) (16970511553/40000000000 : ℝ) (212131394417/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4317/32768 : ℝ))) 1 (589999456991/1000000000000 : ℝ) (117999891399/200000000000 : ℝ) (16970511553/40000000000 : ℝ) (212131394417/500000000000 : ℝ) (126782780727/250000000000 : ℝ) (101426224583/200000000000 : ℝ) (250157357991/500000000000 : ℝ) (50031471599/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4317/32768 : ℝ))) 2 (126782780727/250000000000 : ℝ) (101426224583/200000000000 : ℝ) (250157357991/500000000000 : ℝ) (50031471599/100000000000 : ℝ) (100744583889/200000000000 : ℝ) (503722919453/1000000000000 : ℝ) (3935245229/7812500000 : ℝ) (503711389321/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4317/32768 : ℝ))) 3 (100744583889/200000000000 : ℝ) (503722919453/1000000000000 : ℝ) (3935245229/7812500000 : ℝ) (503711389321/1000000000000 : ℝ) (251858577189/500000000000 : ℝ) (503717154387/1000000000000 : ℝ) (100743430869/200000000000 : ℝ) (100743430871/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4317/32768 : ℝ))) 4 (251858577189/500000000000 : ℝ) (503717154387/1000000000000 : ℝ) (100743430869/200000000000 : ℝ) (100743430871/200000000000 : ℝ) (503717154361/1000000000000 : ℝ) (503717154371/1000000000000 : ℝ) (503717154361/1000000000000 : ℝ) (503717154371/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4317/32768 : ℝ))) 5 (503717154361/1000000000000 : ℝ) (503717154371/1000000000000 : ℝ) (503717154361/1000000000000 : ℝ) (503717154371/1000000000000 : ℝ) (503717154361/1000000000000 : ℝ) (503717154371/1000000000000 : ℝ) (503717154361/1000000000000 : ℝ) (503717154371/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4317/32768 : ℝ))) 6 (503717154361/1000000000000 : ℝ) (503717154371/1000000000000 : ℝ) (503717154361/1000000000000 : ℝ) (503717154371/1000000000000 : ℝ) (503717154361/1000000000000 : ℝ) (503717154371/1000000000000 : ℝ) (503717154361/1000000000000 : ℝ) (503717154371/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4317/32768 : ℝ))) 7 (503717154361/1000000000000 : ℝ) (503717154371/1000000000000 : ℝ) (503717154361/1000000000000 : ℝ) (503717154371/1000000000000 : ℝ) (503717154361/1000000000000 : ℝ) (503717154371/1000000000000 : ℝ) (503717154361/1000000000000 : ℝ) (503717154371/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4317/32768 : ℝ)) hmem 8 (495908296747/500000000000 : ℝ) (991816593497/1000000000000 : ℝ) (495908296747/500000000000 : ℝ) (991816593497/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4317/32768 : ℝ))) hcmem 8 (503717154361/1000000000000 : ℝ) (503717154371/1000000000000 : ℝ) (503717154361/1000000000000 : ℝ) (503717154371/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4317/32768 : ℝ)) (495908296747/500000000000 : ℝ) (991816593497/1000000000000 : ℝ) (503717154361/1000000000000 : ℝ) (503717154371/1000000000000 : ℝ) (398882747577/500000000000 : ℝ) (398882747587/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1597_exp_lower
  have heNumeric : (1027465975091/500000000000 : ℝ)/4 ≤ Real.exp (-1332103255973/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027465975091/500000000000 : ℝ)/4 ≤ Real.exp ((1079/8192 : ℝ)-(398882747587/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1079/8192 : ℝ) (4317/32768 : ℝ) (398882747587/500000000000 : ℝ) (1027465975091/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1598; no trusted numerical premise.
theorem cover8_leaf1598_exp_radius : (199588627080400347/200000000000000000 : ℝ) ≤ Real.exp ((-2159/131072 : ℝ)/8) ∧ Real.exp ((-2159/131072 : ℝ)/8) ≤ (124742891925250217/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2159/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1598_exp_lower : (23002880612451527/25000000000000000 : ℝ) ≤ Real.exp ((-1065681571351/1600000000000 : ℝ)/8) ∧ Real.exp ((-1065681571351/1600000000000 : ℝ)/8) ≤ (920115224498061081/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1065681571351/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1598_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054933277447/1000000000000 : ℝ) ≤ 4*Real.exp (4317/32768 : ℝ)*Real.exp (-mu (radius 8 (2159/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054933277447/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2159/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1598_exp_radius
  have hrNumeric : (245915764133/250000000000 : ℝ) ≤ Real.exp (-2159/131072 : ℝ) ∧ Real.exp (-2159/131072 : ℝ) ≤ (983663056533/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245915764133/250000000000 : ℝ) ≤ (radius 8 (2159/16384 : ℝ)) ∧ (radius 8 (2159/16384 : ℝ)) ≤ (983663056533/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2159/16384 : ℝ)) (245915764133/250000000000 : ℝ) (983663056533/1000000000000 : ℝ) (90009709493/500000000000 : ℝ) (11251213687/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2159/16384 : ℝ)) (245915764133/250000000000 : ℝ) (983663056533/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2159/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245915764133/250000000000 : ℝ) (983663056533/1000000000000 : ℝ) (495915764133/500000000000 : ℝ) (991831528267/1000000000000 : ℝ) (991797890969/1000000000000 : ℝ) (991797890971/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2159/16384 : ℝ)) 1 (495915764133/500000000000 : ℝ) (991831528267/1000000000000 : ℝ) (991797890969/1000000000000 : ℝ) (991797890971/1000000000000 : ℝ) (991814709617/1000000000000 : ℝ) (991814709619/1000000000000 : ℝ) (495907354737/500000000000 : ℝ) (991814709477/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2159/16384 : ℝ)) 2 (991814709617/1000000000000 : ℝ) (991814709619/1000000000000 : ℝ) (495907354737/500000000000 : ℝ) (991814709477/1000000000000 : ℝ) (198362941909/200000000000 : ℝ) (247953677387/250000000000 : ℝ) (198362941909/200000000000 : ℝ) (247953677387/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2159/16384 : ℝ)) 3 (198362941909/200000000000 : ℝ) (247953677387/250000000000 : ℝ) (198362941909/200000000000 : ℝ) (247953677387/250000000000 : ℝ) (198362941909/200000000000 : ℝ) (247953677387/250000000000 : ℝ) (198362941909/200000000000 : ℝ) (247953677387/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2159/16384 : ℝ)) 4 (198362941909/200000000000 : ℝ) (247953677387/250000000000 : ℝ) (198362941909/200000000000 : ℝ) (247953677387/250000000000 : ℝ) (198362941909/200000000000 : ℝ) (247953677387/250000000000 : ℝ) (198362941909/200000000000 : ℝ) (247953677387/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2159/16384 : ℝ)) 5 (198362941909/200000000000 : ℝ) (247953677387/250000000000 : ℝ) (198362941909/200000000000 : ℝ) (247953677387/250000000000 : ℝ) (198362941909/200000000000 : ℝ) (247953677387/250000000000 : ℝ) (198362941909/200000000000 : ℝ) (247953677387/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2159/16384 : ℝ)) 6 (198362941909/200000000000 : ℝ) (247953677387/250000000000 : ℝ) (198362941909/200000000000 : ℝ) (247953677387/250000000000 : ℝ) (198362941909/200000000000 : ℝ) (247953677387/250000000000 : ℝ) (198362941909/200000000000 : ℝ) (247953677387/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2159/16384 : ℝ)) 7 (198362941909/200000000000 : ℝ) (247953677387/250000000000 : ℝ) (198362941909/200000000000 : ℝ) (247953677387/250000000000 : ℝ) (198362941909/200000000000 : ℝ) (247953677387/250000000000 : ℝ) (198362941909/200000000000 : ℝ) (247953677387/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2159/16384 : ℝ))) (90009709493/500000000000 : ℝ) (11251213687/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2159/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (90009709493/500000000000 : ℝ) (11251213687/62500000000 : ℝ) (590009709493/1000000000000 : ℝ) (73751213687/125000000000 : ℝ) (424286953589/1000000000000 : ℝ) (424286953597/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2159/16384 : ℝ))) 1 (590009709493/1000000000000 : ℝ) (73751213687/125000000000 : ℝ) (424286953589/1000000000000 : ℝ) (424286953597/1000000000000 : ℝ) (507148331541/1000000000000 : ℝ) (507148331547/1000000000000 : ℝ) (125083327783/250000000000 : ℝ) (500333311139/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2159/16384 : ℝ))) 2 (507148331541/1000000000000 : ℝ) (507148331547/1000000000000 : ℝ) (125083327783/250000000000 : ℝ) (500333311139/1000000000000 : ℝ) (62967602667/125000000000 : ℝ) (503740821343/1000000000000 : ℝ) (31483081019/62500000000 : ℝ) (503729296311/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2159/16384 : ℝ))) 3 (62967602667/125000000000 : ℝ) (503740821343/1000000000000 : ℝ) (31483081019/62500000000 : ℝ) (503729296311/1000000000000 : ℝ) (25186752941/50000000000 : ℝ) (503735058827/1000000000000 : ℝ) (503735058787/1000000000000 : ℝ) (100747011759/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2159/16384 : ℝ))) 4 (25186752941/50000000000 : ℝ) (503735058827/1000000000000 : ℝ) (503735058787/1000000000000 : ℝ) (100747011759/200000000000 : ℝ) (503735058803/1000000000000 : ℝ) (503735058811/1000000000000 : ℝ) (503735058803/1000000000000 : ℝ) (503735058811/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2159/16384 : ℝ))) 5 (503735058803/1000000000000 : ℝ) (503735058811/1000000000000 : ℝ) (503735058803/1000000000000 : ℝ) (503735058811/1000000000000 : ℝ) (503735058803/1000000000000 : ℝ) (503735058811/1000000000000 : ℝ) (503735058803/1000000000000 : ℝ) (503735058811/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2159/16384 : ℝ))) 6 (503735058803/1000000000000 : ℝ) (503735058811/1000000000000 : ℝ) (503735058803/1000000000000 : ℝ) (503735058811/1000000000000 : ℝ) (503735058803/1000000000000 : ℝ) (503735058811/1000000000000 : ℝ) (503735058803/1000000000000 : ℝ) (503735058811/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2159/16384 : ℝ))) 7 (503735058803/1000000000000 : ℝ) (503735058811/1000000000000 : ℝ) (503735058803/1000000000000 : ℝ) (503735058811/1000000000000 : ℝ) (503735058803/1000000000000 : ℝ) (503735058811/1000000000000 : ℝ) (503735058803/1000000000000 : ℝ) (503735058811/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2159/16384 : ℝ)) hmem 8 (198362941909/200000000000 : ℝ) (247953677387/250000000000 : ℝ) (198362941909/200000000000 : ℝ) (247953677387/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2159/16384 : ℝ))) hcmem 8 (503735058803/1000000000000 : ℝ) (503735058811/1000000000000 : ℝ) (503735058803/1000000000000 : ℝ) (503735058811/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2159/16384 : ℝ)) (198362941909/200000000000 : ℝ) (247953677387/250000000000 : ℝ) (503735058803/1000000000000 : ℝ) (503735058811/1000000000000 : ℝ) (199448841711/250000000000 : ℝ) (39889768343/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1598_exp_lower
  have heNumeric : (2054933277447/1000000000000 : ℝ)/4 ≤ Real.exp (-1065681571351/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054933277447/1000000000000 : ℝ)/4 ≤ Real.exp ((4317/32768 : ℝ)-(39889768343/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4317/32768 : ℝ) (2159/16384 : ℝ) (39889768343/50000000000 : ℝ) (2054933277447/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1599; no trusted numerical premise.
theorem cover8_leaf1599_exp_radius : (199588531909149291/200000000000000000 : ℝ) ≤ Real.exp ((-4319/262144 : ℝ)/8) ∧ Real.exp ((-4319/262144 : ℝ)/8) ≤ (124742832443218307/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4319/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1599_exp_lower : (920115299322653657/1000000000000000000 : ℝ) ≤ Real.exp ((-2664201326109/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664201326109/4000000000000 : ℝ)/8) ≤ (460057649661326829/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664201326109/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1599_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054934614319/1000000000000 : ℝ) ≤ 4*Real.exp (2159/16384 : ℝ)*Real.exp (-mu (radius 8 (4319/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054934614319/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4319/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1599_exp_radius
  have hrNumeric : (491829652081/500000000000 : ℝ) ≤ Real.exp (-4319/262144 : ℝ) ∧ Real.exp (-4319/262144 : ℝ) ≤ (983659304163/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491829652081/500000000000 : ℝ) ≤ (radius 8 (4319/32768 : ℝ)) ∧ (radius 8 (4319/32768 : ℝ)) ≤ (983659304163/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4319/32768 : ℝ)) (491829652081/500000000000 : ℝ) (983659304163/1000000000000 : ℝ) (180039921499/1000000000000 : ℝ) (90019960753/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4319/32768 : ℝ)) (491829652081/500000000000 : ℝ) (983659304163/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4319/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491829652081/500000000000 : ℝ) (983659304163/1000000000000 : ℝ) (991829652081/1000000000000 : ℝ) (495914826041/500000000000 : ℝ) (495897999633/500000000000 : ℝ) (247948999817/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4319/32768 : ℝ)) 1 (991829652081/1000000000000 : ℝ) (495914826041/500000000000 : ℝ) (495897999633/500000000000 : ℝ) (247948999817/250000000000 : ℝ) (991812825673/1000000000000 : ℝ) (39672513027/40000000000 : ℝ) (99181282553/100000000000 : ℝ) (991812825533/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4319/32768 : ℝ)) 2 (991812825673/1000000000000 : ℝ) (39672513027/40000000000 : ℝ) (99181282553/100000000000 : ℝ) (991812825533/1000000000000 : ℝ) (991812825601/1000000000000 : ℝ) (247953206401/250000000000 : ℝ) (991812825601/1000000000000 : ℝ) (247953206401/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4319/32768 : ℝ)) 3 (991812825601/1000000000000 : ℝ) (247953206401/250000000000 : ℝ) (991812825601/1000000000000 : ℝ) (247953206401/250000000000 : ℝ) (991812825601/1000000000000 : ℝ) (247953206401/250000000000 : ℝ) (991812825601/1000000000000 : ℝ) (247953206401/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4319/32768 : ℝ)) 4 (991812825601/1000000000000 : ℝ) (247953206401/250000000000 : ℝ) (991812825601/1000000000000 : ℝ) (247953206401/250000000000 : ℝ) (991812825601/1000000000000 : ℝ) (247953206401/250000000000 : ℝ) (991812825601/1000000000000 : ℝ) (247953206401/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4319/32768 : ℝ)) 5 (991812825601/1000000000000 : ℝ) (247953206401/250000000000 : ℝ) (991812825601/1000000000000 : ℝ) (247953206401/250000000000 : ℝ) (991812825601/1000000000000 : ℝ) (247953206401/250000000000 : ℝ) (991812825601/1000000000000 : ℝ) (247953206401/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4319/32768 : ℝ)) 6 (991812825601/1000000000000 : ℝ) (247953206401/250000000000 : ℝ) (991812825601/1000000000000 : ℝ) (247953206401/250000000000 : ℝ) (991812825601/1000000000000 : ℝ) (247953206401/250000000000 : ℝ) (991812825601/1000000000000 : ℝ) (247953206401/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4319/32768 : ℝ)) 7 (991812825601/1000000000000 : ℝ) (247953206401/250000000000 : ℝ) (991812825601/1000000000000 : ℝ) (247953206401/250000000000 : ℝ) (991812825601/1000000000000 : ℝ) (247953206401/250000000000 : ℝ) (991812825601/1000000000000 : ℝ) (247953206401/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4319/32768 : ℝ))) (180039921499/1000000000000 : ℝ) (90019960753/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4319/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (180039921499/1000000000000 : ℝ) (90019960753/500000000000 : ℝ) (590019960749/1000000000000 : ℝ) (590019960753/1000000000000 : ℝ) (424311114041/1000000000000 : ℝ) (8486222281/20000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4319/32768 : ℝ))) 1 (590019960749/1000000000000 : ℝ) (590019960753/1000000000000 : ℝ) (424311114041/1000000000000 : ℝ) (8486222281/20000000000 : ℝ) (101433107479/200000000000 : ℝ) (253582768701/500000000000 : ℝ) (62543987877/125000000000 : ℝ) (31271993939/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4319/32768 : ℝ))) 2 (101433107479/200000000000 : ℝ) (253582768701/500000000000 : ℝ) (62543987877/125000000000 : ℝ) (31271993939/62500000000 : ℝ) (100751744041/200000000000 : ℝ) (503758720213/1000000000000 : ℝ) (503747200269/1000000000000 : ℝ) (251873600139/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4319/32768 : ℝ))) 3 (100751744041/200000000000 : ℝ) (503758720213/1000000000000 : ℝ) (503747200269/1000000000000 : ℝ) (251873600139/500000000000 : ℝ) (503752960237/1000000000000 : ℝ) (251876480123/500000000000 : ℝ) (125938240051/250000000000 : ℝ) (503752960213/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4319/32768 : ℝ))) 4 (503752960237/1000000000000 : ℝ) (251876480123/500000000000 : ℝ) (125938240051/250000000000 : ℝ) (503752960213/1000000000000 : ℝ) (25187648011/50000000000 : ℝ) (50375296023/100000000000 : ℝ) (25187648011/50000000000 : ℝ) (50375296023/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4319/32768 : ℝ))) 5 (25187648011/50000000000 : ℝ) (50375296023/100000000000 : ℝ) (25187648011/50000000000 : ℝ) (50375296023/100000000000 : ℝ) (25187648011/50000000000 : ℝ) (50375296023/100000000000 : ℝ) (25187648011/50000000000 : ℝ) (50375296023/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4319/32768 : ℝ))) 6 (25187648011/50000000000 : ℝ) (50375296023/100000000000 : ℝ) (25187648011/50000000000 : ℝ) (50375296023/100000000000 : ℝ) (25187648011/50000000000 : ℝ) (50375296023/100000000000 : ℝ) (25187648011/50000000000 : ℝ) (50375296023/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4319/32768 : ℝ))) 7 (25187648011/50000000000 : ℝ) (50375296023/100000000000 : ℝ) (25187648011/50000000000 : ℝ) (50375296023/100000000000 : ℝ) (25187648011/50000000000 : ℝ) (50375296023/100000000000 : ℝ) (25187648011/50000000000 : ℝ) (50375296023/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4319/32768 : ℝ)) hmem 8 (991812825601/1000000000000 : ℝ) (247953206401/250000000000 : ℝ) (991812825601/1000000000000 : ℝ) (247953206401/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4319/32768 : ℝ))) hcmem 8 (25187648011/50000000000 : ℝ) (50375296023/100000000000 : ℝ) (25187648011/50000000000 : ℝ) (50375296023/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4319/32768 : ℝ)) (991812825601/1000000000000 : ℝ) (247953206401/250000000000 : ℝ) (25187648011/50000000000 : ℝ) (50375296023/100000000000 : ℝ) (199456308463/250000000000 : ℝ) (797825233871/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1599_exp_lower
  have heNumeric : (2054934614319/1000000000000 : ℝ)/4 ≤ Real.exp (-2664201326109/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054934614319/1000000000000 : ℝ)/4 ≤ Real.exp ((2159/16384 : ℝ)-(797825233871/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2159/16384 : ℝ) (4319/32768 : ℝ) (797825233871/1000000000000 : ℝ) (2054934614319/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf1575_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1575_certificate
#check SmaleRate.Proofs.cover8_leaf1576_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1576_certificate
#check SmaleRate.Proofs.cover8_leaf1577_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1577_certificate
#check SmaleRate.Proofs.cover8_leaf1578_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1578_certificate
#check SmaleRate.Proofs.cover8_leaf1579_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1579_certificate
#check SmaleRate.Proofs.cover8_leaf1580_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1580_certificate
#check SmaleRate.Proofs.cover8_leaf1581_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1581_certificate
#check SmaleRate.Proofs.cover8_leaf1582_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1582_certificate
#check SmaleRate.Proofs.cover8_leaf1583_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1583_certificate
#check SmaleRate.Proofs.cover8_leaf1584_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1584_certificate
#check SmaleRate.Proofs.cover8_leaf1585_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1585_certificate
#check SmaleRate.Proofs.cover8_leaf1586_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1586_certificate
#check SmaleRate.Proofs.cover8_leaf1587_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1587_certificate
#check SmaleRate.Proofs.cover8_leaf1588_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1588_certificate
#check SmaleRate.Proofs.cover8_leaf1589_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1589_certificate
#check SmaleRate.Proofs.cover8_leaf1590_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1590_certificate
#check SmaleRate.Proofs.cover8_leaf1591_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1591_certificate
#check SmaleRate.Proofs.cover8_leaf1592_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1592_certificate
#check SmaleRate.Proofs.cover8_leaf1593_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1593_certificate
#check SmaleRate.Proofs.cover8_leaf1594_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1594_certificate
#check SmaleRate.Proofs.cover8_leaf1595_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1595_certificate
#check SmaleRate.Proofs.cover8_leaf1596_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1596_certificate
#check SmaleRate.Proofs.cover8_leaf1597_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1597_certificate
#check SmaleRate.Proofs.cover8_leaf1598_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1598_certificate
#check SmaleRate.Proofs.cover8_leaf1599_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1599_certificate
