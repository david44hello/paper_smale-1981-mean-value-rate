/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.FiniteBoxSoundness
public import SmaleRate.Proofs.Generated.D7Tree0000
public import SmaleRate.Proofs.Generated.D7Tree0001
public import SmaleRate.Proofs.Generated.D7Tree0002
public import SmaleRate.Proofs.Generated.D7Tree0003
public import SmaleRate.Proofs.Generated.D7Tree0004
public import SmaleRate.Proofs.Generated.D7Tree0005
public import SmaleRate.Proofs.Generated.D7Tree0006
public import SmaleRate.Proofs.Generated.D7Tree0007
public import SmaleRate.Proofs.Generated.D7Tree0008
public import SmaleRate.Proofs.Generated.D7Tree0009
public import SmaleRate.Proofs.Generated.D7Tree0010
public import SmaleRate.Proofs.Generated.D7Tree0011
public import SmaleRate.Proofs.Generated.D7Tree0012
public import SmaleRate.Proofs.Generated.D7Tree0013
public import SmaleRate.Proofs.Generated.D7Tree0014
public import SmaleRate.Proofs.Generated.D7Tree0015
public import SmaleRate.Proofs.Generated.D7Tree0016
public import SmaleRate.Proofs.Generated.D7Tree0017
public import SmaleRate.Proofs.Generated.D7Tree0018
public import SmaleRate.Proofs.Generated.D7Tree0019
public import SmaleRate.Proofs.Generated.D7Tree0020
public import SmaleRate.Proofs.Generated.D7Tree0021
public import SmaleRate.Proofs.Generated.D7Tree0022
public import SmaleRate.Proofs.Generated.D7Tree0023
public import SmaleRate.Proofs.Generated.D7Tree0024
public import SmaleRate.Proofs.Generated.D7Tree0025
public import SmaleRate.Proofs.Generated.D7Tree0026
public import SmaleRate.Proofs.Generated.D7Tree0027
public import SmaleRate.Proofs.Generated.D7Tree0028
public import SmaleRate.Proofs.Generated.D7Tree0029
public import SmaleRate.Proofs.Generated.D7Tree0030
public import SmaleRate.Proofs.Generated.D7Tree0031
public import SmaleRate.Proofs.Generated.D7Tree0032
public import SmaleRate.Proofs.Generated.D7Tree0033
public import SmaleRate.Proofs.Generated.D7Tree0034
public import SmaleRate.Proofs.Generated.D7Tree0035
public import SmaleRate.Proofs.Generated.D7Tree0036
public import SmaleRate.Proofs.Generated.D7Tree0037
public import SmaleRate.Proofs.Generated.D7Tree0038
public import SmaleRate.Proofs.Generated.D7Tree0039
public import SmaleRate.Proofs.Generated.D7Tree0040
public import SmaleRate.Proofs.Generated.D7Tree0041
public import SmaleRate.Proofs.Generated.D7Tree0042

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover7_tree : BoxTree := (.split (.split (.split (.split cover7_tree0000 (.split cover7_tree0001 (.split cover7_tree0002 (.split cover7_tree0003 cover7_tree0004)))) (.split (.split (.split (.split (.split cover7_tree0005 (.split cover7_tree0006 (.split cover7_tree0007 (.split cover7_tree0008 cover7_tree0009)))) (.split (.split (.split (.split cover7_tree0010 cover7_tree0011) (.split cover7_tree0012 (.split cover7_tree0013 cover7_tree0014))) (.split (.split (.split cover7_tree0015 cover7_tree0016) (.split cover7_tree0017 cover7_tree0018)) (.split (.split cover7_tree0019 cover7_tree0020) (.split cover7_tree0021 cover7_tree0022)))) (.split (.split (.split (.split cover7_tree0023 cover7_tree0024) (.split cover7_tree0025 cover7_tree0026)) (.split (.split cover7_tree0027 cover7_tree0028) cover7_tree0029)) (.split (.split cover7_tree0030 cover7_tree0031) (.split cover7_tree0032 cover7_tree0033))))) (.split (.split (.split (.split cover7_tree0034 cover7_tree0035) cover7_tree0036) cover7_tree0037) cover7_tree0038)) cover7_tree0039) cover7_tree0040)) cover7_tree0041) cover7_tree0042)

theorem cover7_tree_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree 0 1 := by
  unfold cover7_tree
  refine tree_all_split_at (1/2 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (1/4 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (1/8 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (1/16 : ℚ) (by norm_num) ?_ ?_
        · simpa only [div_one] using cover7_tree0000_checked hidentity
        · refine tree_all_split_at (3/32 : ℚ) (by norm_num) ?_ ?_
          · exact cover7_tree0001_checked hidentity
          · refine tree_all_split_at (7/64 : ℚ) (by norm_num) ?_ ?_
            · exact cover7_tree0002_checked hidentity
            · refine tree_all_split_at (15/128 : ℚ) (by norm_num) ?_ ?_
              · exact cover7_tree0003_checked hidentity
              · exact cover7_tree0004_checked hidentity
      · refine tree_all_split_at (3/16 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (5/32 : ℚ) (by norm_num) ?_ ?_
          · refine tree_all_split_at (9/64 : ℚ) (by norm_num) ?_ ?_
            · refine tree_all_split_at (17/128 : ℚ) (by norm_num) ?_ ?_
              · refine tree_all_split_at (33/256 : ℚ) (by norm_num) ?_ ?_
                · exact cover7_tree0005_checked hidentity
                · refine tree_all_split_at (67/512 : ℚ) (by norm_num) ?_ ?_
                  · exact cover7_tree0006_checked hidentity
                  · refine tree_all_split_at (135/1024 : ℚ) (by norm_num) ?_ ?_
                    · exact cover7_tree0007_checked hidentity
                    · refine tree_all_split_at (271/2048 : ℚ) (by norm_num) ?_ ?_
                      · exact cover7_tree0008_checked hidentity
                      · exact cover7_tree0009_checked hidentity
              · refine tree_all_split_at (35/256 : ℚ) (by norm_num) ?_ ?_
                · refine tree_all_split_at (69/512 : ℚ) (by norm_num) ?_ ?_
                  · refine tree_all_split_at (137/1024 : ℚ) (by norm_num) ?_ ?_
                    · refine tree_all_split_at (273/2048 : ℚ) (by norm_num) ?_ ?_
                      · exact cover7_tree0010_checked hidentity
                      · exact cover7_tree0011_checked hidentity
                    · refine tree_all_split_at (275/2048 : ℚ) (by norm_num) ?_ ?_
                      · exact cover7_tree0012_checked hidentity
                      · refine tree_all_split_at (551/4096 : ℚ) (by norm_num) ?_ ?_
                        · exact cover7_tree0013_checked hidentity
                        · exact cover7_tree0014_checked hidentity
                  · refine tree_all_split_at (139/1024 : ℚ) (by norm_num) ?_ ?_
                    · refine tree_all_split_at (277/2048 : ℚ) (by norm_num) ?_ ?_
                      · refine tree_all_split_at (553/4096 : ℚ) (by norm_num) ?_ ?_
                        · exact cover7_tree0015_checked hidentity
                        · exact cover7_tree0016_checked hidentity
                      · refine tree_all_split_at (555/4096 : ℚ) (by norm_num) ?_ ?_
                        · exact cover7_tree0017_checked hidentity
                        · exact cover7_tree0018_checked hidentity
                    · refine tree_all_split_at (279/2048 : ℚ) (by norm_num) ?_ ?_
                      · refine tree_all_split_at (557/4096 : ℚ) (by norm_num) ?_ ?_
                        · exact cover7_tree0019_checked hidentity
                        · exact cover7_tree0020_checked hidentity
                      · refine tree_all_split_at (559/4096 : ℚ) (by norm_num) ?_ ?_
                        · exact cover7_tree0021_checked hidentity
                        · exact cover7_tree0022_checked hidentity
                · refine tree_all_split_at (71/512 : ℚ) (by norm_num) ?_ ?_
                  · refine tree_all_split_at (141/1024 : ℚ) (by norm_num) ?_ ?_
                    · refine tree_all_split_at (281/2048 : ℚ) (by norm_num) ?_ ?_
                      · refine tree_all_split_at (561/4096 : ℚ) (by norm_num) ?_ ?_
                        · exact cover7_tree0023_checked hidentity
                        · exact cover7_tree0024_checked hidentity
                      · refine tree_all_split_at (563/4096 : ℚ) (by norm_num) ?_ ?_
                        · exact cover7_tree0025_checked hidentity
                        · exact cover7_tree0026_checked hidentity
                    · refine tree_all_split_at (283/2048 : ℚ) (by norm_num) ?_ ?_
                      · refine tree_all_split_at (565/4096 : ℚ) (by norm_num) ?_ ?_
                        · exact cover7_tree0027_checked hidentity
                        · exact cover7_tree0028_checked hidentity
                      · exact cover7_tree0029_checked hidentity
                  · refine tree_all_split_at (143/1024 : ℚ) (by norm_num) ?_ ?_
                    · refine tree_all_split_at (285/2048 : ℚ) (by norm_num) ?_ ?_
                      · exact cover7_tree0030_checked hidentity
                      · exact cover7_tree0031_checked hidentity
                    · refine tree_all_split_at (287/2048 : ℚ) (by norm_num) ?_ ?_
                      · exact cover7_tree0032_checked hidentity
                      · exact cover7_tree0033_checked hidentity
            · refine tree_all_split_at (19/128 : ℚ) (by norm_num) ?_ ?_
              · refine tree_all_split_at (37/256 : ℚ) (by norm_num) ?_ ?_
                · refine tree_all_split_at (73/512 : ℚ) (by norm_num) ?_ ?_
                  · refine tree_all_split_at (145/1024 : ℚ) (by norm_num) ?_ ?_
                    · exact cover7_tree0034_checked hidentity
                    · exact cover7_tree0035_checked hidentity
                  · exact cover7_tree0036_checked hidentity
                · exact cover7_tree0037_checked hidentity
              · exact cover7_tree0038_checked hidentity
          · exact cover7_tree0039_checked hidentity
        · exact cover7_tree0040_checked hidentity
    · exact cover7_tree0041_checked hidentity
  · simpa only [div_one] using cover7_tree0042_checked hidentity

theorem cover7_best_bound_lower
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus)))
    (hdlmf : ∀ modulus ∈ Ioo (0 : ℝ) 1,
      Real.log ((1 + Real.sqrt (complement modulus))^2 / modulus) < mu modulus ∧
      mu modulus < Real.log (2 * (1 + complement modulus) / modulus)) :
    (2019/1000 : ℝ) < bestBound 7 := by
  have hcover := dyadic_unit_cover cover7_tree
  have hleaves := (tree_boxes_all (fun box => BoxEndpointBound 7 box ∧ (2019/1000 : ℝ) < (box.lower : ℝ)) cover7_tree 0 1).mpr (cover7_tree_checked hidentity)
  refine finite_box_soundness_from_dlmf hdlmf 7 (by omega)
    (treeBoxes cover7_tree 0 1) hcover.1 hcover.2.2 hcover.2.1
    (fun box hbox => (hleaves box hbox).1) (2019/1000 : ℝ)
    (fun box hbox => (hleaves box hbox).2) ?_
  have hexp := exp_lower_eight (6/7 : ℝ) (by norm_num)
  norm_num [Finset.sum_range_succ] at hexp
  linarith

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_best_bound_lower
#print axioms SmaleRate.Proofs.cover7_best_bound_lower
