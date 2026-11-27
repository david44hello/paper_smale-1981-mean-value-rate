/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import SmaleRate.Proofs.AGMAnalytic
public import SmaleRate.Proofs.TableCertificates

set_option backward.proofsInPublic true

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

def AgmInterval (modulus : ℝ) (index : ℕ) (lowerA upperA lowerB upperB : ℝ) : Prop :=
  (lowerA ≤ (agmPair modulus index).1 ∧ (agmPair modulus index).1 ≤ upperA) ∧
    (lowerB ≤ (agmPair modulus index).2 ∧ (agmPair modulus index).2 ≤ upperB)

theorem agm_interval_zero (modulus lower upper : ℝ) (hbound : lower ≤ modulus ∧ modulus ≤ upper) :
    AgmInterval modulus 0 1 1 lower upper := by
  simpa only [AgmInterval, agmPair] using And.intro (And.intro (le_refl (1 : ℝ)) (le_refl (1 : ℝ))) hbound

theorem agm_interval_step (modulus : ℝ) (index : ℕ)
    (lowerA upperA lowerB upperB nextLowerA nextUpperA nextLowerB nextUpperB : ℝ)
    (hbound : AgmInterval modulus index lowerA upperA lowerB upperB)
    (hLowerA : 0 ≤ lowerA) (hLowerB : 0 ≤ lowerB)
    (hnextLowerA : nextLowerA ≤ (lowerA+lowerB)/2)
    (hnextUpperA : (upperA+upperB)/2 ≤ nextUpperA)
    (hnextLowerB : 0 ≤ nextLowerB) (hnextUpperB : 0 ≤ nextUpperB)
    (hsquareLower : nextLowerB^2 ≤ lowerA*lowerB)
    (hsquareUpper : upperA*upperB ≤ nextUpperB^2) :
    AgmInterval modulus (index+1) nextLowerA nextUpperA nextLowerB nextUpperB := by
  rcases hbound with ⟨⟨haLower, haUpper⟩, ⟨hbLower, hbUpper⟩⟩
  have haNonneg := hLowerA.trans haLower
  have hbNonneg := hLowerB.trans hbLower
  have hupperANonneg := haNonneg.trans haUpper
  have hproductLower : lowerA*lowerB ≤ (agmPair modulus index).1*(agmPair modulus index).2 :=
    mul_le_mul haLower hbLower hLowerB haNonneg
  have hproductUpper : (agmPair modulus index).1*(agmPair modulus index).2 ≤ upperA*upperB :=
    mul_le_mul haUpper hbUpper hbNonneg hupperANonneg
  unfold AgmInterval
  simp only [agmPair]
  refine ⟨⟨by linarith, by linarith⟩, ?_, ?_⟩
  · exact Real.le_sqrt_of_sq_le (hsquareLower.trans hproductLower)
  · exact (Real.sqrt_le_left hnextUpperB).2 (hproductUpper.trans hsquareUpper)

theorem complement_interval_of_radius (modulus lower upper compLower compUpper : ℝ)
    (hmodulus : modulus ∈ Ioo 0 1) (hbound : lower ≤ modulus ∧ modulus ≤ upper)
    (hlower : 0 ≤ lower) (hcompLower : 0 ≤ compLower) (hcompUpper : 0 ≤ compUpper)
    (hsquareLower : compLower^2 ≤ 1-upper^2)
    (hsquareUpper : 1-lower^2 ≤ compUpper^2) :
    compLower ≤ complement modulus ∧ complement modulus ≤ compUpper := by
  have hmNonneg := hmodulus.1.le
  have huNonneg := hmNonneg.trans hbound.2
  have hlowSquare : lower^2 ≤ modulus^2 := by gcongr; exact hbound.1
  have huppSquare : modulus^2 ≤ upper^2 := by gcongr; exact hbound.2
  unfold complement
  constructor
  · exact Real.le_sqrt_of_sq_le (by linarith)
  · exact (Real.sqrt_le_left hcompUpper).2 (by linarith)

theorem agm_bounds_of_interval (modulus : ℝ) (hmodulus : modulus ∈ Ioo 0 1) (index : ℕ)
    (lowerA upperA lowerB upperB : ℝ) (hbound : AgmInterval modulus index lowerA upperA lowerB upperB) :
    lowerB ≤ agm modulus ∧ agm modulus ≤ upperA := by
  have hactual := agm_sandwich modulus hmodulus index
  exact ⟨hbound.2.1.trans hactual.1, hactual.2.trans hbound.1.2⟩

theorem mu_interval_of_agm (modulus lowerR upperR lowerComp upperComp lowerMu upperMu : ℝ)
    (hmodulus : modulus ∈ Ioo 0 1)
    (hidentity : mu modulus = Real.pi*agm (complement modulus)/(2*agm modulus))
    (hr : lowerR ≤ agm modulus ∧ agm modulus ≤ upperR)
    (hc : lowerComp ≤ agm (complement modulus) ∧ agm (complement modulus) ≤ upperComp)
    (hrpos : 0 < lowerR) (hcpos : 0 ≤ lowerComp)
    (hLower : lowerMu ≤ (314159265358979323846/100000000000000000000 : ℝ)*lowerComp/(2*upperR))
    (hUpper : (314159265358979323847/100000000000000000000 : ℝ)*upperComp/(2*lowerR) ≤ upperMu) :
    lowerMu ≤ mu modulus ∧ mu modulus ≤ upperMu := by
  have hagmpos := hrpos.trans_le hr.1
  have hupperRpos := hagmpos.trans_le hr.2
  have hcompNonneg := hcpos.trans hc.1
  have hupperCompNonneg := hcompNonneg.trans hc.2
  have hpiLower : (314159265358979323846/100000000000000000000 : ℝ) ≤ Real.pi := by
    linarith [Real.pi_gt_d20]
  have hpiUpper : Real.pi ≤ (314159265358979323847/100000000000000000000 : ℝ) := by
    linarith [Real.pi_lt_d20]
  have hnumLower : (314159265358979323846/100000000000000000000 : ℝ)*lowerComp ≤
      Real.pi*agm (complement modulus) :=
    mul_le_mul hpiLower hc.1 hcpos Real.pi_pos.le
  have hnumUpper : Real.pi*agm (complement modulus) ≤
      (314159265358979323847/100000000000000000000 : ℝ)*upperComp :=
    mul_le_mul hpiUpper hc.2 hcompNonneg (by norm_num)
  rw [hidentity]
  constructor
  · apply hLower.trans
    exact div_le_div₀ (by positivity) hnumLower (by positivity) (by linarith [hr.2])
  · apply le_trans _ hUpper
    exact div_le_div₀ (by positivity) hnumUpper (by positivity) (by linarith [hr.1])

theorem beta_upper_of_mu_interval (degree : ℕ) (length lowerMu bound : ℝ)
    (hmu : lowerMu ≤ mu (radius degree length)) (hexp : Real.exp (length-lowerMu) ≤ bound/4) :
    beta degree length ≤ bound := by
  unfold beta
  have h := Real.exp_le_exp.mpr (sub_le_sub_left hmu length)
  linarith

theorem box_endpoint_lower_of_mu_interval (degree : ℕ) (left right upperMu bound : ℝ)
    (hmu : mu (radius degree right) ≤ upperMu) (hexp : bound/4 ≤ Real.exp (left-upperMu)) :
    bound ≤ 4*Real.exp left*Real.exp (-mu (radius degree right)) := by
  have h := Real.exp_le_exp.mpr (sub_le_sub_left hmu left)
  have hid : Real.exp (left-mu (radius degree right)) = Real.exp left*Real.exp (-mu (radius degree right)) := by
    rw [show left-mu (radius degree right) = left+(-mu (radius degree right)) by ring, Real.exp_add]
  rw [mul_assoc, ← hid]
  linarith

-- Proposed record trialbox8; no trusted numerical premise.
theorem trialbox8_exp_radius : (199601460113406829/200000000000000000 : ℝ) ≤ Real.exp ((-6383/400000 : ℝ)/8) ∧ Real.exp ((-6383/400000 : ℝ)/8) ≤ (499003650283517073/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-6383/400000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem trialbox8_exp_upper : (28753552093783109/31250000000000000 : ℝ) ≤ Real.exp ((-333032261931/500000000000 : ℝ)/8) ∧ Real.exp ((-333032261931/500000000000 : ℝ)/8) ≤ (920113667001059489/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-333032261931/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem trialbox8_exp_lower : (460056778656392103/500000000000000000 : ℝ) ≤ Real.exp ((-170512762254161/256000000000000 : ℝ)/8) ∧ Real.exp ((-170512762254161/256000000000000 : ℝ)/8) ≤ (920113557312784207/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-170512762254161/256000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem trialbox8_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903490457/1000000000000 : ℝ) ≤ 4*Real.exp (418313163/3276800000 : ℝ)*Real.exp (-mu (radius 8 (6383/50000 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903490457/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (6383/50000 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) trialbox8_exp_radius
  have hrNumeric : (196833829271/200000000000 : ℝ) ≤ Real.exp (-6383/400000 : ℝ) ∧ Real.exp (-6383/400000 : ℝ) ≤ (246042286589/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196833829271/200000000000 : ℝ) ≤ (radius 8 (6383/50000 : ℝ)) ∧ (radius 8 (6383/50000 : ℝ)) ≤ (246042286589/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (6383/50000 : ℝ)) (196833829271/200000000000 : ℝ) (246042286589/250000000000 : ℝ) (44307936197/250000000000 : ℝ) (35446348959/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (6383/50000 : ℝ)) (196833829271/200000000000 : ℝ) (246042286589/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (6383/50000 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196833829271/200000000000 : ℝ) (246042286589/250000000000 : ℝ) (992084573177/1000000000000 : ℝ) (496042286589/500000000000 : ℝ) (992052995739/1000000000000 : ℝ) (49602649787/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (6383/50000 : ℝ)) 1 (992084573177/1000000000000 : ℝ) (496042286589/500000000000 : ℝ) (992052995739/1000000000000 : ℝ) (49602649787/50000000000 : ℝ) (496034392229/500000000000 : ℝ) (992068784459/1000000000000 : ℝ) (248017196083/250000000000 : ℝ) (496034392167/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (6383/50000 : ℝ)) 2 (496034392229/500000000000 : ℝ) (992068784459/1000000000000 : ℝ) (248017196083/250000000000 : ℝ) (496034392167/500000000000 : ℝ) (198413756879/200000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (6383/50000 : ℝ)) 3 (198413756879/200000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (6383/50000 : ℝ)) 4 (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (6383/50000 : ℝ)) 5 (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (6383/50000 : ℝ)) 6 (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (6383/50000 : ℝ)) 7 (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (6383/50000 : ℝ))) (44307936197/250000000000 : ℝ) (35446348959/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (6383/50000 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44307936197/250000000000 : ℝ) (35446348959/200000000000 : ℝ) (294307936197/500000000000 : ℝ) (294307936199/500000000000 : ℝ) (210494503959/500000000000 : ℝ) (420989007927/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (6383/50000 : ℝ))) 1 (294307936197/500000000000 : ℝ) (294307936199/500000000000 : ℝ) (210494503959/500000000000 : ℝ) (420989007927/1000000000000 : ℝ) (126200610039/250000000000 : ℝ) (504802440163/1000000000000 : ℝ) (248897977173/500000000000 : ℝ) (248897977177/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (6383/50000 : ℝ))) 2 (126200610039/250000000000 : ℝ) (504802440163/1000000000000 : ℝ) (248897977173/500000000000 : ℝ) (248897977177/500000000000 : ℝ) (501299197251/1000000000000 : ℝ) (501299197259/1000000000000 : ℝ) (501286956197/1000000000000 : ℝ) (100257391241/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (6383/50000 : ℝ))) 3 (501299197251/1000000000000 : ℝ) (501299197259/1000000000000 : ℝ) (501286956197/1000000000000 : ℝ) (100257391241/200000000000 : ℝ) (125323269181/250000000000 : ℝ) (125323269183/250000000000 : ℝ) (250646538343/500000000000 : ℝ) (100258615339/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (6383/50000 : ℝ))) 4 (125323269181/250000000000 : ℝ) (125323269183/250000000000 : ℝ) (250646538343/500000000000 : ℝ) (100258615339/200000000000 : ℝ) (100258615341/200000000000 : ℝ) (250646538357/500000000000 : ℝ) (15665408647/31250000000 : ℝ) (250646538357/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (6383/50000 : ℝ))) 5 (100258615341/200000000000 : ℝ) (250646538357/500000000000 : ℝ) (15665408647/31250000000 : ℝ) (250646538357/500000000000 : ℝ) (15665408647/31250000000 : ℝ) (250646538357/500000000000 : ℝ) (15665408647/31250000000 : ℝ) (250646538357/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (6383/50000 : ℝ))) 6 (15665408647/31250000000 : ℝ) (250646538357/500000000000 : ℝ) (15665408647/31250000000 : ℝ) (250646538357/500000000000 : ℝ) (15665408647/31250000000 : ℝ) (250646538357/500000000000 : ℝ) (15665408647/31250000000 : ℝ) (250646538357/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (6383/50000 : ℝ))) 7 (15665408647/31250000000 : ℝ) (250646538357/500000000000 : ℝ) (15665408647/31250000000 : ℝ) (250646538357/500000000000 : ℝ) (15665408647/31250000000 : ℝ) (250646538357/500000000000 : ℝ) (15665408647/31250000000 : ℝ) (250646538357/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (6383/50000 : ℝ)) hmem 8 (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (6383/50000 : ℝ))) hcmem 8 (15665408647/31250000000 : ℝ) (250646538357/500000000000 : ℝ) (15665408647/31250000000 : ℝ) (250646538357/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (6383/50000 : ℝ)) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (15665408647/31250000000 : ℝ) (250646538357/500000000000 : ℝ) (396862261931/500000000000 : ℝ) (793724523881/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) trialbox8_exp_lower
  have heNumeric : (2054903490457/1000000000000 : ℝ)/4 ≤ Real.exp (-170512762254161/256000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903490457/1000000000000 : ℝ)/4 ≤ Real.exp ((418313163/3276800000 : ℝ)-(793724523881/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (418313163/3276800000 : ℝ) (6383/50000 : ℝ) (793724523881/1000000000000 : ℝ) (2054903490457/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Verified AGM endpoint bounds.
-- Version 0.10; every inequality needs its kernel proof.
-- Proposed record point7; no trusted numerical premise.
theorem point7_exp_radius : (997570634268307241/1000000000000000000 : ℝ) ≤ Real.exp ((-13621/700000 : ℝ)/8) ∧ Real.exp ((-13621/700000 : ℝ)/8) ≤ (498785317134153621/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-13621/700000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem point7_exp_upper : (229522693830109411/250000000000000000 : ℝ) ≤ Real.exp ((-85459009459/125000000000 : ℝ)/8) ∧ Real.exp ((-85459009459/125000000000 : ℝ)/8) ≤ (183618155064087529/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85459009459/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem point7_exp_lower : (45904538765918597/50000000000000000 : ℝ) ≤ Real.exp ((-68367207569/100000000000 : ℝ)/8) ∧ Real.exp ((-68367207569/100000000000 : ℝ)/8) ≤ (918090775318371941/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-68367207569/100000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem point7_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    beta 7 (13621/100000 : ℝ) < (20191/10000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (13621/100000 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) point7_exp_radius
  have hrNumeric : (98072952457/100000000000 : ℝ) ≤ Real.exp (-13621/700000 : ℝ) ∧ Real.exp (-13621/700000 : ℝ) ≤ (980729524571/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98072952457/100000000000 : ℝ) ≤ (radius 7 (13621/100000 : ℝ)) ∧ (radius 7 (13621/100000 : ℝ)) ≤ (980729524571/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (13621/100000 : ℝ)) (98072952457/100000000000 : ℝ) (980729524571/1000000000000 : ℝ) (195370416477/1000000000000 : ℝ) (195370416483/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (13621/100000 : ℝ)) (98072952457/100000000000 : ℝ) (980729524571/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (13621/100000 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98072952457/100000000000 : ℝ) (980729524571/1000000000000 : ℝ) (198072952457/200000000000 : ℝ) (495182381143/500000000000 : ℝ) (123789736333/125000000000 : ℝ) (198063578133/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (13621/100000 : ℝ)) 1 (198072952457/200000000000 : ℝ) (495182381143/500000000000 : ℝ) (123789736333/125000000000 : ℝ) (198063578133/200000000000 : ℝ) (495170663237/500000000000 : ℝ) (247585331619/250000000000 : ℝ) (990341326197/1000000000000 : ℝ) (990341326199/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (13621/100000 : ℝ)) 2 (495170663237/500000000000 : ℝ) (247585331619/250000000000 : ℝ) (990341326197/1000000000000 : ℝ) (990341326199/1000000000000 : ℝ) (198068265267/200000000000 : ℝ) (495170663169/500000000000 : ℝ) (198068265267/200000000000 : ℝ) (495170663169/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (13621/100000 : ℝ)) 3 (198068265267/200000000000 : ℝ) (495170663169/500000000000 : ℝ) (198068265267/200000000000 : ℝ) (495170663169/500000000000 : ℝ) (198068265267/200000000000 : ℝ) (495170663169/500000000000 : ℝ) (198068265267/200000000000 : ℝ) (495170663169/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (13621/100000 : ℝ)) 4 (198068265267/200000000000 : ℝ) (495170663169/500000000000 : ℝ) (198068265267/200000000000 : ℝ) (495170663169/500000000000 : ℝ) (198068265267/200000000000 : ℝ) (495170663169/500000000000 : ℝ) (198068265267/200000000000 : ℝ) (495170663169/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (13621/100000 : ℝ)) 5 (198068265267/200000000000 : ℝ) (495170663169/500000000000 : ℝ) (198068265267/200000000000 : ℝ) (495170663169/500000000000 : ℝ) (198068265267/200000000000 : ℝ) (495170663169/500000000000 : ℝ) (198068265267/200000000000 : ℝ) (495170663169/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (13621/100000 : ℝ)) 6 (198068265267/200000000000 : ℝ) (495170663169/500000000000 : ℝ) (198068265267/200000000000 : ℝ) (495170663169/500000000000 : ℝ) (198068265267/200000000000 : ℝ) (495170663169/500000000000 : ℝ) (198068265267/200000000000 : ℝ) (495170663169/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (13621/100000 : ℝ)) 7 (198068265267/200000000000 : ℝ) (495170663169/500000000000 : ℝ) (198068265267/200000000000 : ℝ) (495170663169/500000000000 : ℝ) (198068265267/200000000000 : ℝ) (495170663169/500000000000 : ℝ) (198068265267/200000000000 : ℝ) (495170663169/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (13621/100000 : ℝ))) (195370416477/1000000000000 : ℝ) (195370416483/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (13621/100000 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195370416477/1000000000000 : ℝ) (195370416483/1000000000000 : ℝ) (298842604119/500000000000 : ℝ) (298842604121/500000000000 : ℝ) (221003629199/500000000000 : ℝ) (221003629203/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (13621/100000 : ℝ))) 1 (298842604119/500000000000 : ℝ) (298842604121/500000000000 : ℝ) (221003629199/500000000000 : ℝ) (221003629203/500000000000 : ℝ) (259923116659/500000000000 : ℝ) (129961558331/250000000000 : ℝ) (513985603181/1000000000000 : ℝ) (513985603189/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (13621/100000 : ℝ))) 2 (259923116659/500000000000 : ℝ) (129961558331/250000000000 : ℝ) (513985603181/1000000000000 : ℝ) (513985603189/1000000000000 : ℝ) (516915918249/1000000000000 : ℝ) (516915918257/1000000000000 : ℝ) (103381522487/200000000000 : ℝ) (516907612443/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (13621/100000 : ℝ))) 3 (516915918249/1000000000000 : ℝ) (516915918257/1000000000000 : ℝ) (103381522487/200000000000 : ℝ) (516907612443/1000000000000 : ℝ) (258455882671/500000000000 : ℝ) (10338235307/20000000000 : ℝ) (20676470613/40000000000 : ℝ) (258455882667/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (13621/100000 : ℝ))) 4 (258455882671/500000000000 : ℝ) (10338235307/20000000000 : ℝ) (20676470613/40000000000 : ℝ) (258455882667/500000000000 : ℝ) (516911765333/1000000000000 : ℝ) (258455882671/500000000000 : ℝ) (516911765333/1000000000000 : ℝ) (258455882671/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (13621/100000 : ℝ))) 5 (516911765333/1000000000000 : ℝ) (258455882671/500000000000 : ℝ) (516911765333/1000000000000 : ℝ) (258455882671/500000000000 : ℝ) (516911765333/1000000000000 : ℝ) (258455882671/500000000000 : ℝ) (516911765333/1000000000000 : ℝ) (258455882671/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (13621/100000 : ℝ))) 6 (516911765333/1000000000000 : ℝ) (258455882671/500000000000 : ℝ) (516911765333/1000000000000 : ℝ) (258455882671/500000000000 : ℝ) (516911765333/1000000000000 : ℝ) (258455882671/500000000000 : ℝ) (516911765333/1000000000000 : ℝ) (258455882671/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (13621/100000 : ℝ))) 7 (516911765333/1000000000000 : ℝ) (258455882671/500000000000 : ℝ) (516911765333/1000000000000 : ℝ) (258455882671/500000000000 : ℝ) (516911765333/1000000000000 : ℝ) (258455882671/500000000000 : ℝ) (516911765333/1000000000000 : ℝ) (258455882671/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (13621/100000 : ℝ)) hmem 8 (198068265267/200000000000 : ℝ) (495170663169/500000000000 : ℝ) (198068265267/200000000000 : ℝ) (495170663169/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (13621/100000 : ℝ))) hcmem 8 (516911765333/1000000000000 : ℝ) (258455882671/500000000000 : ℝ) (516911765333/1000000000000 : ℝ) (258455882671/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (13621/100000 : ℝ)) (198068265267/200000000000 : ℝ) (495170663169/500000000000 : ℝ) (516911765333/1000000000000 : ℝ) (258455882671/500000000000 : ℝ) (102485259459/125000000000 : ℝ) (81988207569/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) point7_exp_upper
  have huNumeric : Real.exp (-85459009459/125000000000 : ℝ) < (20191/10000 : ℝ)/4 := he.2.trans_lt (by norm_num)
  have hu : Real.exp ((13621/100000 : ℝ)-(102485259459/125000000000 : ℝ)) < (20191/10000 : ℝ)/4 := by
    convert huNumeric using 1 <;> norm_num
  have hm := Real.exp_le_exp.mpr (sub_le_sub_left hmu.1 (13621/100000 : ℝ))
  unfold beta
  linarith
-- Proposed record point8; no trusted numerical premise.
theorem point8_exp_radius : (199601460113406829/200000000000000000 : ℝ) ≤ Real.exp ((-6383/400000 : ℝ)/8) ∧ Real.exp ((-6383/400000 : ℝ)/8) ≤ (499003650283517073/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-6383/400000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem point8_exp_upper : (28753552093783109/31250000000000000 : ℝ) ≤ Real.exp ((-333032261931/500000000000 : ℝ)/8) ∧ Real.exp ((-333032261931/500000000000 : ℝ)/8) ≤ (920113667001059489/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-333032261931/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem point8_exp_lower : (460056833499437109/500000000000000000 : ℝ) ≤ Real.exp ((-666064523881/1000000000000 : ℝ)/8) ∧ Real.exp ((-666064523881/1000000000000 : ℝ)/8) ≤ (920113666998874219/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666064523881/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem point8_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    beta 8 (6383/50000 : ℝ) < (411/200 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (6383/50000 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) point8_exp_radius
  have hrNumeric : (196833829271/200000000000 : ℝ) ≤ Real.exp (-6383/400000 : ℝ) ∧ Real.exp (-6383/400000 : ℝ) ≤ (246042286589/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196833829271/200000000000 : ℝ) ≤ (radius 8 (6383/50000 : ℝ)) ∧ (radius 8 (6383/50000 : ℝ)) ≤ (246042286589/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (6383/50000 : ℝ)) (196833829271/200000000000 : ℝ) (246042286589/250000000000 : ℝ) (44307936197/250000000000 : ℝ) (35446348959/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (6383/50000 : ℝ)) (196833829271/200000000000 : ℝ) (246042286589/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (6383/50000 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196833829271/200000000000 : ℝ) (246042286589/250000000000 : ℝ) (992084573177/1000000000000 : ℝ) (496042286589/500000000000 : ℝ) (992052995739/1000000000000 : ℝ) (49602649787/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (6383/50000 : ℝ)) 1 (992084573177/1000000000000 : ℝ) (496042286589/500000000000 : ℝ) (992052995739/1000000000000 : ℝ) (49602649787/50000000000 : ℝ) (496034392229/500000000000 : ℝ) (992068784459/1000000000000 : ℝ) (248017196083/250000000000 : ℝ) (496034392167/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (6383/50000 : ℝ)) 2 (496034392229/500000000000 : ℝ) (992068784459/1000000000000 : ℝ) (248017196083/250000000000 : ℝ) (496034392167/500000000000 : ℝ) (198413756879/200000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (6383/50000 : ℝ)) 3 (198413756879/200000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (6383/50000 : ℝ)) 4 (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (6383/50000 : ℝ)) 5 (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (6383/50000 : ℝ)) 6 (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (6383/50000 : ℝ)) 7 (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (6383/50000 : ℝ))) (44307936197/250000000000 : ℝ) (35446348959/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (6383/50000 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44307936197/250000000000 : ℝ) (35446348959/200000000000 : ℝ) (294307936197/500000000000 : ℝ) (294307936199/500000000000 : ℝ) (210494503959/500000000000 : ℝ) (420989007927/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (6383/50000 : ℝ))) 1 (294307936197/500000000000 : ℝ) (294307936199/500000000000 : ℝ) (210494503959/500000000000 : ℝ) (420989007927/1000000000000 : ℝ) (126200610039/250000000000 : ℝ) (504802440163/1000000000000 : ℝ) (248897977173/500000000000 : ℝ) (248897977177/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (6383/50000 : ℝ))) 2 (126200610039/250000000000 : ℝ) (504802440163/1000000000000 : ℝ) (248897977173/500000000000 : ℝ) (248897977177/500000000000 : ℝ) (501299197251/1000000000000 : ℝ) (501299197259/1000000000000 : ℝ) (501286956197/1000000000000 : ℝ) (100257391241/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (6383/50000 : ℝ))) 3 (501299197251/1000000000000 : ℝ) (501299197259/1000000000000 : ℝ) (501286956197/1000000000000 : ℝ) (100257391241/200000000000 : ℝ) (125323269181/250000000000 : ℝ) (125323269183/250000000000 : ℝ) (250646538343/500000000000 : ℝ) (100258615339/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (6383/50000 : ℝ))) 4 (125323269181/250000000000 : ℝ) (125323269183/250000000000 : ℝ) (250646538343/500000000000 : ℝ) (100258615339/200000000000 : ℝ) (100258615341/200000000000 : ℝ) (250646538357/500000000000 : ℝ) (15665408647/31250000000 : ℝ) (250646538357/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (6383/50000 : ℝ))) 5 (100258615341/200000000000 : ℝ) (250646538357/500000000000 : ℝ) (15665408647/31250000000 : ℝ) (250646538357/500000000000 : ℝ) (15665408647/31250000000 : ℝ) (250646538357/500000000000 : ℝ) (15665408647/31250000000 : ℝ) (250646538357/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (6383/50000 : ℝ))) 6 (15665408647/31250000000 : ℝ) (250646538357/500000000000 : ℝ) (15665408647/31250000000 : ℝ) (250646538357/500000000000 : ℝ) (15665408647/31250000000 : ℝ) (250646538357/500000000000 : ℝ) (15665408647/31250000000 : ℝ) (250646538357/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (6383/50000 : ℝ))) 7 (15665408647/31250000000 : ℝ) (250646538357/500000000000 : ℝ) (15665408647/31250000000 : ℝ) (250646538357/500000000000 : ℝ) (15665408647/31250000000 : ℝ) (250646538357/500000000000 : ℝ) (15665408647/31250000000 : ℝ) (250646538357/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (6383/50000 : ℝ)) hmem 8 (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (6383/50000 : ℝ))) hcmem 8 (15665408647/31250000000 : ℝ) (250646538357/500000000000 : ℝ) (15665408647/31250000000 : ℝ) (250646538357/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (6383/50000 : ℝ)) (496034392197/500000000000 : ℝ) (992068784397/1000000000000 : ℝ) (15665408647/31250000000 : ℝ) (250646538357/500000000000 : ℝ) (396862261931/500000000000 : ℝ) (793724523881/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) point8_exp_upper
  have huNumeric : Real.exp (-333032261931/500000000000 : ℝ) < (411/200 : ℝ)/4 := he.2.trans_lt (by norm_num)
  have hu : Real.exp ((6383/50000 : ℝ)-(396862261931/500000000000 : ℝ)) < (411/200 : ℝ)/4 := by
    convert huNumeric using 1 <;> norm_num
  have hm := Real.exp_le_exp.mpr (sub_le_sub_left hmu.1 (6383/50000 : ℝ))
  unfold beta
  linarith
-- Proposed record point100; no trusted numerical premise.
theorem point100_exp_radius : (31247915303913417/31250000000000000 : ℝ) ≤ Real.exp ((-5337/10000000 : ℝ)/8) ∧ Real.exp ((-5337/10000000 : ℝ)/8) ≤ (199986657945045869/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5337/10000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem point100_exp_upper : (472068991075549741/500000000000000000 : ℝ) ≤ Real.exp ((-459863647881/1000000000000 : ℝ)/8) ∧ Real.exp ((-459863647881/1000000000000 : ℝ)/8) ≤ (944137982151099483/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-459863647881/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem point100_exp_lower : (236034495534411379/250000000000000000 : ℝ) ≤ Real.exp ((-91972729599/200000000000 : ℝ)/8) ∧ Real.exp ((-91972729599/200000000000 : ℝ)/8) ≤ (944137982137645517/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-91972729599/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem point100_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    beta 100 (5337/100000 : ℝ) < (5051/2000 : ℝ) := by
  have hmem := radius_mem 100 (by norm_num) (5337/100000 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) point100_exp_radius
  have hrNumeric : (124933305299/125000000000 : ℝ) ≤ Real.exp (-5337/10000000 : ℝ) ∧ Real.exp (-5337/10000000 : ℝ) ≤ (999466442393/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (124933305299/125000000000 : ℝ) ≤ (radius 100 (5337/100000 : ℝ)) ∧ (radius 100 (5337/100000 : ℝ)) ≤ (999466442393/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 100 (5337/100000 : ℝ)) (124933305299/125000000000 : ℝ) (999466442393/1000000000000 : ℝ) (32662371779/1000000000000 : ℝ) (32662371811/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 100 (5337/100000 : ℝ)) (124933305299/125000000000 : ℝ) (999466442393/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 100 (5337/100000 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (124933305299/125000000000 : ℝ) (999466442393/1000000000000 : ℝ) (249933305299/250000000000 : ℝ) (999733221197/1000000000000 : ℝ) (999733185601/1000000000000 : ℝ) (499866592801/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 100 (5337/100000 : ℝ)) 1 (249933305299/250000000000 : ℝ) (999733221197/1000000000000 : ℝ) (999733185601/1000000000000 : ℝ) (499866592801/500000000000 : ℝ) (499866601699/500000000000 : ℝ) (4998666017/5000000000 : ℝ) (499866601699/500000000000 : ℝ) (4998666017/5000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 100 (5337/100000 : ℝ)) 2 (499866601699/500000000000 : ℝ) (4998666017/5000000000 : ℝ) (499866601699/500000000000 : ℝ) (4998666017/5000000000 : ℝ) (499866601699/500000000000 : ℝ) (4998666017/5000000000 : ℝ) (499866601699/500000000000 : ℝ) (4998666017/5000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 100 (5337/100000 : ℝ)) 3 (499866601699/500000000000 : ℝ) (4998666017/5000000000 : ℝ) (499866601699/500000000000 : ℝ) (4998666017/5000000000 : ℝ) (499866601699/500000000000 : ℝ) (4998666017/5000000000 : ℝ) (499866601699/500000000000 : ℝ) (4998666017/5000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 100 (5337/100000 : ℝ)) 4 (499866601699/500000000000 : ℝ) (4998666017/5000000000 : ℝ) (499866601699/500000000000 : ℝ) (4998666017/5000000000 : ℝ) (499866601699/500000000000 : ℝ) (4998666017/5000000000 : ℝ) (499866601699/500000000000 : ℝ) (4998666017/5000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 100 (5337/100000 : ℝ)) 5 (499866601699/500000000000 : ℝ) (4998666017/5000000000 : ℝ) (499866601699/500000000000 : ℝ) (4998666017/5000000000 : ℝ) (499866601699/500000000000 : ℝ) (4998666017/5000000000 : ℝ) (499866601699/500000000000 : ℝ) (4998666017/5000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 100 (5337/100000 : ℝ)) 6 (499866601699/500000000000 : ℝ) (4998666017/5000000000 : ℝ) (499866601699/500000000000 : ℝ) (4998666017/5000000000 : ℝ) (499866601699/500000000000 : ℝ) (4998666017/5000000000 : ℝ) (499866601699/500000000000 : ℝ) (4998666017/5000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 100 (5337/100000 : ℝ)) 7 (499866601699/500000000000 : ℝ) (4998666017/5000000000 : ℝ) (499866601699/500000000000 : ℝ) (4998666017/5000000000 : ℝ) (499866601699/500000000000 : ℝ) (4998666017/5000000000 : ℝ) (499866601699/500000000000 : ℝ) (4998666017/5000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 100 (5337/100000 : ℝ))) (32662371779/1000000000000 : ℝ) (32662371811/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 100 (5337/100000 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (32662371779/1000000000000 : ℝ) (32662371811/1000000000000 : ℝ) (516331185889/1000000000000 : ℝ) (258165592953/500000000000 : ℝ) (180727340983/1000000000000 : ℝ) (180727341073/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 100 (5337/100000 : ℝ))) 1 (516331185889/1000000000000 : ℝ) (258165592953/500000000000 : ℝ) (180727340983/1000000000000 : ℝ) (180727341073/1000000000000 : ℝ) (87132315859/250000000000 : ℝ) (34852926349/100000000000 : ℝ) (4773051649/15625000000 : ℝ) (152737652809/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 100 (5337/100000 : ℝ))) 2 (87132315859/250000000000 : ℝ) (34852926349/100000000000 : ℝ) (4773051649/15625000000 : ℝ) (152737652809/500000000000 : ℝ) (163501142243/500000000000 : ℝ) (163501142277/500000000000 : ℝ) (326292940831/1000000000000 : ℝ) (326292940901/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 100 (5337/100000 : ℝ))) 3 (163501142243/500000000000 : ℝ) (163501142277/500000000000 : ℝ) (326292940831/1000000000000 : ℝ) (326292940901/1000000000000 : ℝ) (163323806329/500000000000 : ℝ) (40830951591/125000000000 : ℝ) (81661855027/250000000000 : ℝ) (163323710089/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 100 (5337/100000 : ℝ))) 4 (163323806329/500000000000 : ℝ) (40830951591/125000000000 : ℝ) (81661855027/250000000000 : ℝ) (163323710089/500000000000 : ℝ) (326647516383/1000000000000 : ℝ) (326647516453/1000000000000 : ℝ) (163323758191/500000000000 : ℝ) (326647516453/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 100 (5337/100000 : ℝ))) 5 (326647516383/1000000000000 : ℝ) (326647516453/1000000000000 : ℝ) (163323758191/500000000000 : ℝ) (326647516453/1000000000000 : ℝ) (163323758191/500000000000 : ℝ) (326647516453/1000000000000 : ℝ) (163323758191/500000000000 : ℝ) (326647516453/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 100 (5337/100000 : ℝ))) 6 (163323758191/500000000000 : ℝ) (326647516453/1000000000000 : ℝ) (163323758191/500000000000 : ℝ) (326647516453/1000000000000 : ℝ) (163323758191/500000000000 : ℝ) (326647516453/1000000000000 : ℝ) (163323758191/500000000000 : ℝ) (326647516453/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 100 (5337/100000 : ℝ))) 7 (163323758191/500000000000 : ℝ) (326647516453/1000000000000 : ℝ) (163323758191/500000000000 : ℝ) (326647516453/1000000000000 : ℝ) (163323758191/500000000000 : ℝ) (326647516453/1000000000000 : ℝ) (163323758191/500000000000 : ℝ) (326647516453/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 100 (5337/100000 : ℝ)) hmem 8 (499866601699/500000000000 : ℝ) (4998666017/5000000000 : ℝ) (499866601699/500000000000 : ℝ) (4998666017/5000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 100 (5337/100000 : ℝ))) hcmem 8 (163323758191/500000000000 : ℝ) (326647516453/1000000000000 : ℝ) (163323758191/500000000000 : ℝ) (326647516453/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 100 (5337/100000 : ℝ)) (499866601699/500000000000 : ℝ) (4998666017/5000000000 : ℝ) (163323758191/500000000000 : ℝ) (326647516453/1000000000000 : ℝ) (513233647881/1000000000000 : ℝ) (102646729599/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) point100_exp_upper
  have huNumeric : Real.exp (-459863647881/1000000000000 : ℝ) < (5051/2000 : ℝ)/4 := he.2.trans_lt (by norm_num)
  have hu : Real.exp ((5337/100000 : ℝ)-(513233647881/1000000000000 : ℝ)) < (5051/2000 : ℝ)/4 := by
    convert huNumeric using 1 <;> norm_num
  have hm := Real.exp_le_exp.mpr (sub_le_sub_left hmu.1 (5337/100000 : ℝ))
  unfold beta
  linarith
-- Proposed record point10000; no trusted numerical premise.
theorem point10000_exp_radius : (199999946100007263/200000000000000000 : ℝ) ≤ Real.exp ((-539/250000000 : ℝ)/8) ∧ Real.exp ((-539/250000000 : ℝ)/8) ≤ (249999932625009079/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-539/250000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem point10000_exp_upper : (481316080612387619/500000000000000000 : ℝ) ≤ Real.exp ((-38083911883/125000000000 : ℝ)/8) ∧ Real.exp ((-38083911883/125000000000 : ℝ)/8) ≤ (962632161224775239/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-38083911883/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem point10000_exp_lower : (48131608000929857/50000000000000000 : ℝ) ≤ Real.exp ((-2380244571/7812500000 : ℝ)/8) ∧ Real.exp ((-2380244571/7812500000 : ℝ)/8) ≤ (962632160018597141/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2380244571/7812500000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem point10000_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    beta 10000 (539/25000 : ℝ) < (5899/2000 : ℝ) := by
  have hmem := radius_mem 10000 (by norm_num) (539/25000 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) point10000_exp_radius
  have hrNumeric : (499998922001/500000000000 : ℝ) ≤ Real.exp (-539/250000000 : ℝ) ∧ Real.exp (-539/250000000 : ℝ) ≤ (999997844003/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (499998922001/500000000000 : ℝ) ≤ (radius 10000 (539/25000 : ℝ)) ∧ (radius 10000 (539/25000 : ℝ)) ≤ (999997844003/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 10000 (539/25000 : ℝ)) (499998922001/500000000000 : ℝ) (999997844003/1000000000000 : ℝ) (519133253/250000000000 : ℝ) (1038266747/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 10000 (539/25000 : ℝ)) (499998922001/500000000000 : ℝ) (999997844003/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 10000 (539/25000 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (499998922001/500000000000 : ℝ) (999997844003/1000000000000 : ℝ) (999998922001/1000000000000 : ℝ) (499999461001/500000000000 : ℝ) (499999461/500000000 : ℝ) (999998922001/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 10000 (539/25000 : ℝ)) 1 (999998922001/1000000000000 : ℝ) (499999461001/500000000000 : ℝ) (499999461/500000000 : ℝ) (999998922001/1000000000000 : ℝ) (499999461/500000000 : ℝ) (499999461001/500000000000 : ℝ) (499999461/500000000 : ℝ) (499999461001/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 10000 (539/25000 : ℝ)) 2 (499999461/500000000 : ℝ) (499999461001/500000000000 : ℝ) (499999461/500000000 : ℝ) (499999461001/500000000000 : ℝ) (499999461/500000000 : ℝ) (499999461001/500000000000 : ℝ) (499999461/500000000 : ℝ) (499999461001/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 10000 (539/25000 : ℝ)) 3 (499999461/500000000 : ℝ) (499999461001/500000000000 : ℝ) (499999461/500000000 : ℝ) (499999461001/500000000000 : ℝ) (499999461/500000000 : ℝ) (499999461001/500000000000 : ℝ) (499999461/500000000 : ℝ) (499999461001/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 10000 (539/25000 : ℝ)) 4 (499999461/500000000 : ℝ) (499999461001/500000000000 : ℝ) (499999461/500000000 : ℝ) (499999461001/500000000000 : ℝ) (499999461/500000000 : ℝ) (499999461001/500000000000 : ℝ) (499999461/500000000 : ℝ) (499999461001/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 10000 (539/25000 : ℝ)) 5 (499999461/500000000 : ℝ) (499999461001/500000000000 : ℝ) (499999461/500000000 : ℝ) (499999461001/500000000000 : ℝ) (499999461/500000000 : ℝ) (499999461001/500000000000 : ℝ) (499999461/500000000 : ℝ) (499999461001/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 10000 (539/25000 : ℝ)) 6 (499999461/500000000 : ℝ) (499999461001/500000000000 : ℝ) (499999461/500000000 : ℝ) (499999461001/500000000000 : ℝ) (499999461/500000000 : ℝ) (499999461001/500000000000 : ℝ) (499999461/500000000 : ℝ) (499999461001/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 10000 (539/25000 : ℝ)) 7 (499999461/500000000 : ℝ) (499999461001/500000000000 : ℝ) (499999461/500000000 : ℝ) (499999461001/500000000000 : ℝ) (499999461/500000000 : ℝ) (499999461001/500000000000 : ℝ) (499999461/500000000 : ℝ) (499999461001/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 10000 (539/25000 : ℝ))) (519133253/250000000000 : ℝ) (1038266747/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 10000 (539/25000 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (519133253/250000000000 : ℝ) (1038266747/500000000000 : ℝ) (250519133253/500000000000 : ℝ) (501038266747/1000000000000 : ℝ) (45568991781/1000000000000 : ℝ) (45568997071/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 10000 (539/25000 : ℝ))) 1 (250519133253/500000000000 : ℝ) (501038266747/1000000000000 : ℝ) (45568991781/1000000000000 : ℝ) (45568997071/1000000000000 : ℝ) (273303629143/1000000000000 : ℝ) (273303631909/1000000000000 : ℝ) (75550990477/500000000000 : ℝ) (75550994881/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 10000 (539/25000 : ℝ))) 2 (273303629143/1000000000000 : ℝ) (273303631909/1000000000000 : ℝ) (75550990477/500000000000 : ℝ) (75550994881/500000000000 : ℝ) (26525350631/125000000000 : ℝ) (53050702709/250000000000 : ℝ) (203215943679/1000000000000 : ℝ) (203215950631/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 10000 (539/25000 : ℝ))) 3 (26525350631/125000000000 : ℝ) (53050702709/250000000000 : ℝ) (203215943679/1000000000000 : ℝ) (203215950631/1000000000000 : ℝ) (207709374363/1000000000000 : ℝ) (103854690367/500000000000 : ℝ) (2076607649/10000000000 : ℝ) (41532154257/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 10000 (539/25000 : ℝ))) 4 (207709374363/1000000000000 : ℝ) (103854690367/500000000000 : ℝ) (2076607649/10000000000 : ℝ) (41532154257/200000000000 : ℝ) (207685069631/1000000000000 : ℝ) (20768507601/100000000000 : ℝ) (207685068209/1000000000000 : ℝ) (51921268647/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 10000 (539/25000 : ℝ))) 5 (207685069631/1000000000000 : ℝ) (20768507601/100000000000 : ℝ) (207685068209/1000000000000 : ℝ) (51921268647/250000000000 : ℝ) (5192126723/25000000000 : ℝ) (207685075299/1000000000000 : ℝ) (207685068919/1000000000000 : ℝ) (207685075299/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 10000 (539/25000 : ℝ))) 6 (5192126723/25000000000 : ℝ) (207685075299/1000000000000 : ℝ) (207685068919/1000000000000 : ℝ) (207685075299/1000000000000 : ℝ) (207685068919/1000000000000 : ℝ) (207685075299/1000000000000 : ℝ) (207685068919/1000000000000 : ℝ) (207685075299/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 10000 (539/25000 : ℝ))) 7 (207685068919/1000000000000 : ℝ) (207685075299/1000000000000 : ℝ) (207685068919/1000000000000 : ℝ) (207685075299/1000000000000 : ℝ) (207685068919/1000000000000 : ℝ) (207685075299/1000000000000 : ℝ) (207685068919/1000000000000 : ℝ) (207685075299/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 10000 (539/25000 : ℝ)) hmem 8 (499999461/500000000 : ℝ) (499999461001/500000000000 : ℝ) (499999461/500000000 : ℝ) (499999461001/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 10000 (539/25000 : ℝ))) hcmem 8 (207685068919/1000000000000 : ℝ) (207685075299/1000000000000 : ℝ) (207685068919/1000000000000 : ℝ) (207685075299/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 10000 (539/25000 : ℝ)) (499999461/500000000 : ℝ) (499999461001/500000000000 : ℝ) (207685068919/1000000000000 : ℝ) (207685075299/1000000000000 : ℝ) (40778911883/125000000000 : ℝ) (2548682071/7812500000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) point10000_exp_upper
  have huNumeric : Real.exp (-38083911883/125000000000 : ℝ) < (5899/2000 : ℝ)/4 := he.2.trans_lt (by norm_num)
  have hu : Real.exp ((539/25000 : ℝ)-(40778911883/125000000000 : ℝ)) < (5899/2000 : ℝ)/4 := by
    convert huNumeric using 1 <;> norm_num
  have hm := Real.exp_le_exp.mpr (sub_le_sub_left hmu.1 (539/25000 : ℝ))
  unfold beta
  linarith
-- Proposed record point1000000; no trusted numerical premise.
theorem point1000000_exp_radius : (999999998507500001/1000000000000000000 : ℝ) ≤ Real.exp ((-597/50000000000 : ℝ)/8) ∧ Real.exp ((-597/50000000000 : ℝ)/8) ≤ (499999999253750001/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-597/50000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem point1000000_exp_upper : (485776247067685129/500000000000000000 : ℝ) ≤ Real.exp ((-28859977517/125000000000 : ℝ)/8) ∧ Real.exp ((-28859977517/125000000000 : ℝ)/8) ≤ (971552494135370259/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-28859977517/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem point1000000_exp_lower : (485776186294590819/500000000000000000 : ℝ) ≤ Real.exp ((-230880820977/1000000000000 : ℝ)/8) ∧ Real.exp ((-230880820977/1000000000000 : ℝ)/8) ≤ (971552372589181639/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-230880820977/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem point1000000_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    beta 1000000 (597/50000 : ℝ) < (15877/5000 : ℝ) := by
  have hmem := radius_mem 1000000 (by norm_num) (597/50000 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) point1000000_exp_radius
  have hrNumeric : (49999999403/50000000000 : ℝ) ≤ Real.exp (-597/50000000000 : ℝ) ∧ Real.exp (-597/50000000000 : ℝ) ≤ (999999988061/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49999999403/50000000000 : ℝ) ≤ (radius 1000000 (597/50000 : ℝ)) ∧ (radius 1000000 (597/50000 : ℝ)) ≤ (999999988061/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 1000000 (597/50000 : ℝ)) (49999999403/50000000000 : ℝ) (999999988061/1000000000000 : ℝ) (77262539/500000000000 : ℝ) (3090631/20000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 1000000 (597/50000 : ℝ)) (49999999403/50000000000 : ℝ) (999999988061/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 1000000 (597/50000 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49999999403/50000000000 : ℝ) (999999988061/1000000000000 : ℝ) (99999999403/100000000000 : ℝ) (999999994031/1000000000000 : ℝ) (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 1000000 (597/50000 : ℝ)) 1 (99999999403/100000000000 : ℝ) (999999994031/1000000000000 : ℝ) (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ) (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ) (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 1000000 (597/50000 : ℝ)) 2 (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ) (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ) (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ) (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 1000000 (597/50000 : ℝ)) 3 (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ) (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ) (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ) (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 1000000 (597/50000 : ℝ)) 4 (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ) (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ) (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ) (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 1000000 (597/50000 : ℝ)) 5 (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ) (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ) (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ) (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 1000000 (597/50000 : ℝ)) 6 (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ) (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ) (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ) (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 1000000 (597/50000 : ℝ)) 7 (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ) (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ) (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ) (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 1000000 (597/50000 : ℝ))) (77262539/500000000000 : ℝ) (3090631/20000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 1000000 (597/50000 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (77262539/500000000000 : ℝ) (3090631/20000000000 : ℝ) (500077262539/1000000000000 : ℝ) (20003090631/40000000000 : ℝ) (6215405819/500000000000 : ℝ) (12431071957/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 1000000 (597/50000 : ℝ))) 1 (500077262539/1000000000000 : ℝ) (20003090631/40000000000 : ℝ) (6215405819/500000000000 : ℝ) (12431071957/1000000000000 : ℝ) (8007938659/31250000000 : ℝ) (128127084433/500000000000 : ℝ) (7884393607/100000000000 : ℝ) (39422380937/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 1000000 (597/50000 : ℝ))) 2 (8007938659/31250000000 : ℝ) (128127084433/500000000000 : ℝ) (7884393607/100000000000 : ℝ) (39422380937/500000000000 : ℝ) (167548986579/1000000000000 : ℝ) (16754946537/100000000000 : ℝ) (71070522929/500000000000 : ℝ) (142141826791/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 1000000 (597/50000 : ℝ))) 3 (167548986579/1000000000000 : ℝ) (16754946537/100000000000 : ℝ) (71070522929/500000000000 : ℝ) (142141826791/1000000000000 : ℝ) (77422508109/500000000000 : ℝ) (154845646081/1000000000000 : ℝ) (38580749883/250000000000 : ℝ) (77161821981/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 1000000 (597/50000 : ℝ))) 4 (77422508109/500000000000 : ℝ) (154845646081/1000000000000 : ℝ) (38580749883/250000000000 : ℝ) (77161821981/500000000000 : ℝ) (1236672063/8000000000 : ℝ) (77292322511/500000000000 : ℝ) (38645946881/250000000000 : ℝ) (38646106171/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 1000000 (597/50000 : ℝ))) 5 (1236672063/8000000000 : ℝ) (77292322511/500000000000 : ℝ) (38645946881/250000000000 : ℝ) (38646106171/250000000000 : ℝ) (154583897699/1000000000000 : ℝ) (154584534853/1000000000000 : ℝ) (154583897699/1000000000000 : ℝ) (154584534853/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 1000000 (597/50000 : ℝ))) 6 (154583897699/1000000000000 : ℝ) (154584534853/1000000000000 : ℝ) (154583897699/1000000000000 : ℝ) (154584534853/1000000000000 : ℝ) (154583897699/1000000000000 : ℝ) (154584534853/1000000000000 : ℝ) (154583897699/1000000000000 : ℝ) (154584534853/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 1000000 (597/50000 : ℝ))) 7 (154583897699/1000000000000 : ℝ) (154584534853/1000000000000 : ℝ) (154583897699/1000000000000 : ℝ) (154584534853/1000000000000 : ℝ) (154583897699/1000000000000 : ℝ) (154584534853/1000000000000 : ℝ) (154583897699/1000000000000 : ℝ) (154584534853/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 1000000 (597/50000 : ℝ)) hmem 8 (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ) (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 1000000 (597/50000 : ℝ))) hcmem 8 (154583897699/1000000000000 : ℝ) (154584534853/1000000000000 : ℝ) (154583897699/1000000000000 : ℝ) (154584534853/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 1000000 (597/50000 : ℝ)) (999999994029/1000000000000 : ℝ) (999999994031/1000000000000 : ℝ) (154583897699/1000000000000 : ℝ) (154584534853/1000000000000 : ℝ) (30352477517/125000000000 : ℝ) (242820820977/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) point1000000_exp_upper
  have huNumeric : Real.exp (-28859977517/125000000000 : ℝ) < (15877/5000 : ℝ)/4 := he.2.trans_lt (by norm_num)
  have hu : Real.exp ((597/50000 : ℝ)-(30352477517/125000000000 : ℝ)) < (15877/5000 : ℝ)/4 := by
    convert huNumeric using 1 <;> norm_num
  have hm := Real.exp_le_exp.mpr (sub_le_sub_left hmu.1 (597/50000 : ℝ))
  unfold beta
  linarith

end SmaleRate.Proofs

#check SmaleRate.Proofs.agm_interval_step
#print axioms SmaleRate.Proofs.agm_interval_step
#check SmaleRate.Proofs.mu_interval_of_agm
#print axioms SmaleRate.Proofs.mu_interval_of_agm
#check SmaleRate.Proofs.trialbox8_certificate
#print axioms SmaleRate.Proofs.trialbox8_certificate
#check SmaleRate.Proofs.point7_certificate
#print axioms SmaleRate.Proofs.point7_certificate
#check SmaleRate.Proofs.point8_certificate
#print axioms SmaleRate.Proofs.point8_certificate
#check SmaleRate.Proofs.point100_certificate
#print axioms SmaleRate.Proofs.point100_certificate
#check SmaleRate.Proofs.point10000_certificate
#print axioms SmaleRate.Proofs.point10000_certificate
#check SmaleRate.Proofs.point1000000_certificate
#print axioms SmaleRate.Proofs.point1000000_certificate
