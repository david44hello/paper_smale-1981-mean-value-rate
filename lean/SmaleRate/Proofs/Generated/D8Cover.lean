/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.FiniteBoxSoundness
import SmaleRate.Proofs.Generated.D8Tree0000
import SmaleRate.Proofs.Generated.D8Tree0001
import SmaleRate.Proofs.Generated.D8Tree0002
import SmaleRate.Proofs.Generated.D8Tree0003
import SmaleRate.Proofs.Generated.D8Tree0004
import SmaleRate.Proofs.Generated.D8Tree0005
import SmaleRate.Proofs.Generated.D8Tree0006
import SmaleRate.Proofs.Generated.D8Tree0007
import SmaleRate.Proofs.Generated.D8Tree0008
import SmaleRate.Proofs.Generated.D8Tree0009
import SmaleRate.Proofs.Generated.D8Tree0010
import SmaleRate.Proofs.Generated.D8Tree0011
import SmaleRate.Proofs.Generated.D8Tree0012
import SmaleRate.Proofs.Generated.D8Tree0013
import SmaleRate.Proofs.Generated.D8Tree0014
import SmaleRate.Proofs.Generated.D8Tree0015
import SmaleRate.Proofs.Generated.D8Tree0016
import SmaleRate.Proofs.Generated.D8Tree0017
import SmaleRate.Proofs.Generated.D8Tree0018
import SmaleRate.Proofs.Generated.D8Tree0019
import SmaleRate.Proofs.Generated.D8Tree0020
import SmaleRate.Proofs.Generated.D8Tree0021
import SmaleRate.Proofs.Generated.D8Tree0022
import SmaleRate.Proofs.Generated.D8Tree0023
import SmaleRate.Proofs.Generated.D8Tree0024
import SmaleRate.Proofs.Generated.D8Tree0025
import SmaleRate.Proofs.Generated.D8Tree0026
import SmaleRate.Proofs.Generated.D8Tree0027
import SmaleRate.Proofs.Generated.D8Tree0028
import SmaleRate.Proofs.Generated.D8Tree0029
import SmaleRate.Proofs.Generated.D8Tree0030
import SmaleRate.Proofs.Generated.D8Tree0031
import SmaleRate.Proofs.Generated.D8Tree0032
import SmaleRate.Proofs.Generated.D8Tree0033
import SmaleRate.Proofs.Generated.D8Tree0034
import SmaleRate.Proofs.Generated.D8Tree0035
import SmaleRate.Proofs.Generated.D8Tree0036
import SmaleRate.Proofs.Generated.D8Tree0037
import SmaleRate.Proofs.Generated.D8Tree0038
import SmaleRate.Proofs.Generated.D8Tree0039
import SmaleRate.Proofs.Generated.D8Tree0040
import SmaleRate.Proofs.Generated.D8Tree0041
import SmaleRate.Proofs.Generated.D8Tree0042
import SmaleRate.Proofs.Generated.D8Tree0043
import SmaleRate.Proofs.Generated.D8Tree0044
import SmaleRate.Proofs.Generated.D8Tree0045
import SmaleRate.Proofs.Generated.D8Tree0046
import SmaleRate.Proofs.Generated.D8Tree0047
import SmaleRate.Proofs.Generated.D8Tree0048
import SmaleRate.Proofs.Generated.D8Tree0049
import SmaleRate.Proofs.Generated.D8Tree0050
import SmaleRate.Proofs.Generated.D8Tree0051
import SmaleRate.Proofs.Generated.D8Tree0052
import SmaleRate.Proofs.Generated.D8Tree0053
import SmaleRate.Proofs.Generated.D8Tree0054
import SmaleRate.Proofs.Generated.D8Tree0055
import SmaleRate.Proofs.Generated.D8Tree0056
import SmaleRate.Proofs.Generated.D8Tree0057
import SmaleRate.Proofs.Generated.D8Tree0058
import SmaleRate.Proofs.Generated.D8Tree0059
import SmaleRate.Proofs.Generated.D8Tree0060
import SmaleRate.Proofs.Generated.D8Tree0061
import SmaleRate.Proofs.Generated.D8Tree0062
import SmaleRate.Proofs.Generated.D8Tree0063
import SmaleRate.Proofs.Generated.D8Tree0064
import SmaleRate.Proofs.Generated.D8Tree0065
import SmaleRate.Proofs.Generated.D8Tree0066
import SmaleRate.Proofs.Generated.D8Tree0067
import SmaleRate.Proofs.Generated.D8Tree0068
import SmaleRate.Proofs.Generated.D8Tree0069
import SmaleRate.Proofs.Generated.D8Tree0070
import SmaleRate.Proofs.Generated.D8Tree0071
import SmaleRate.Proofs.Generated.D8Tree0072
import SmaleRate.Proofs.Generated.D8Tree0073
import SmaleRate.Proofs.Generated.D8Tree0074
import SmaleRate.Proofs.Generated.D8Tree0075
import SmaleRate.Proofs.Generated.D8Tree0076
import SmaleRate.Proofs.Generated.D8Tree0077
import SmaleRate.Proofs.Generated.D8Tree0078
import SmaleRate.Proofs.Generated.D8Tree0079
import SmaleRate.Proofs.Generated.D8Tree0080
import SmaleRate.Proofs.Generated.D8Tree0081
import SmaleRate.Proofs.Generated.D8Tree0082
import SmaleRate.Proofs.Generated.D8Tree0083
import SmaleRate.Proofs.Generated.D8Tree0084
import SmaleRate.Proofs.Generated.D8Tree0085
import SmaleRate.Proofs.Generated.D8Tree0086
import SmaleRate.Proofs.Generated.D8Tree0087
import SmaleRate.Proofs.Generated.D8Tree0088
import SmaleRate.Proofs.Generated.D8Tree0089
import SmaleRate.Proofs.Generated.D8Tree0090
import SmaleRate.Proofs.Generated.D8Tree0091
import SmaleRate.Proofs.Generated.D8Tree0092
import SmaleRate.Proofs.Generated.D8Tree0093
import SmaleRate.Proofs.Generated.D8Tree0094
import SmaleRate.Proofs.Generated.D8Tree0095
import SmaleRate.Proofs.Generated.D8Tree0096
import SmaleRate.Proofs.Generated.D8Tree0097
import SmaleRate.Proofs.Generated.D8Tree0098
import SmaleRate.Proofs.Generated.D8Tree0099
import SmaleRate.Proofs.Generated.D8Tree0100
import SmaleRate.Proofs.Generated.D8Tree0101
import SmaleRate.Proofs.Generated.D8Tree0102
import SmaleRate.Proofs.Generated.D8Tree0103
import SmaleRate.Proofs.Generated.D8Tree0104
import SmaleRate.Proofs.Generated.D8Tree0105
import SmaleRate.Proofs.Generated.D8Tree0106
import SmaleRate.Proofs.Generated.D8Tree0107
import SmaleRate.Proofs.Generated.D8Tree0108
import SmaleRate.Proofs.Generated.D8Tree0109

noncomputable section
namespace SmaleRate.Proofs
open Set

def cover8_tree : BoxTree := (.split (.split (.split (.split cover8_tree0000 (.split cover8_tree0001 (.split cover8_tree0002 (.split cover8_tree0003 (.split (.split cover8_tree0004 cover8_tree0005) (.split (.split cover8_tree0006 cover8_tree0007) (.split (.split cover8_tree0008 cover8_tree0009) (.split cover8_tree0010 (.split cover8_tree0011 cover8_tree0012))))))))) (.split (.split (.split (.split (.split (.split (.split (.split (.split cover8_tree0013 cover8_tree0014) (.split (.split cover8_tree0015 cover8_tree0016) (.split cover8_tree0017 cover8_tree0018))) (.split (.split (.split cover8_tree0019 cover8_tree0020) (.split cover8_tree0021 (.split cover8_tree0022 cover8_tree0023))) (.split (.split (.split cover8_tree0024 cover8_tree0025) (.split cover8_tree0026 cover8_tree0027)) (.split (.split cover8_tree0028 cover8_tree0029) (.split cover8_tree0030 cover8_tree0031))))) (.split (.split (.split (.split (.split cover8_tree0032 (.split cover8_tree0033 cover8_tree0034)) (.split (.split cover8_tree0035 cover8_tree0036) (.split cover8_tree0037 cover8_tree0038))) (.split (.split (.split cover8_tree0039 cover8_tree0040) (.split cover8_tree0041 cover8_tree0042)) (.split (.split cover8_tree0043 cover8_tree0044) (.split cover8_tree0045 cover8_tree0046)))) (.split (.split (.split (.split cover8_tree0047 cover8_tree0048) (.split cover8_tree0049 cover8_tree0050)) (.split (.split cover8_tree0051 cover8_tree0052) (.split cover8_tree0053 cover8_tree0054))) (.split (.split (.split cover8_tree0055 cover8_tree0056) (.split cover8_tree0057 cover8_tree0058)) (.split (.split cover8_tree0059 cover8_tree0060) (.split cover8_tree0061 cover8_tree0062))))) (.split (.split (.split (.split (.split cover8_tree0063 cover8_tree0064) (.split cover8_tree0065 cover8_tree0066)) (.split (.split cover8_tree0067 cover8_tree0068) (.split cover8_tree0069 cover8_tree0070))) (.split (.split (.split cover8_tree0071 cover8_tree0072) (.split cover8_tree0073 cover8_tree0074)) (.split cover8_tree0075 cover8_tree0076))) (.split (.split (.split cover8_tree0077 cover8_tree0078) (.split cover8_tree0079 cover8_tree0080)) (.split (.split cover8_tree0081 cover8_tree0082) (.split cover8_tree0083 cover8_tree0084)))))) (.split (.split (.split (.split (.split (.split cover8_tree0085 cover8_tree0086) cover8_tree0087) (.split cover8_tree0088 cover8_tree0089)) (.split (.split cover8_tree0090 cover8_tree0091) (.split cover8_tree0092 cover8_tree0093))) (.split (.split cover8_tree0094 cover8_tree0095) (.split cover8_tree0096 cover8_tree0097))) (.split (.split cover8_tree0098 cover8_tree0099) cover8_tree0100))) (.split (.split (.split cover8_tree0101 cover8_tree0102) cover8_tree0103) cover8_tree0104)) cover8_tree0105) cover8_tree0106) cover8_tree0107)) cover8_tree0108) cover8_tree0109)

theorem cover8_tree_checked
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    treeAll (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree 0 1 := by
  unfold cover8_tree
  refine tree_all_split_at (1/2 : ℚ) (by norm_num) ?_ ?_
  · refine tree_all_split_at (1/4 : ℚ) (by norm_num) ?_ ?_
    · refine tree_all_split_at (1/8 : ℚ) (by norm_num) ?_ ?_
      · refine tree_all_split_at (1/16 : ℚ) (by norm_num) ?_ ?_
        · simpa only [div_one] using cover8_tree0000_checked hidentity
        · refine tree_all_split_at (3/32 : ℚ) (by norm_num) ?_ ?_
          · exact cover8_tree0001_checked hidentity
          · refine tree_all_split_at (7/64 : ℚ) (by norm_num) ?_ ?_
            · exact cover8_tree0002_checked hidentity
            · refine tree_all_split_at (15/128 : ℚ) (by norm_num) ?_ ?_
              · exact cover8_tree0003_checked hidentity
              · refine tree_all_split_at (31/256 : ℚ) (by norm_num) ?_ ?_
                · refine tree_all_split_at (61/512 : ℚ) (by norm_num) ?_ ?_
                  · exact cover8_tree0004_checked hidentity
                  · exact cover8_tree0005_checked hidentity
                · refine tree_all_split_at (63/512 : ℚ) (by norm_num) ?_ ?_
                  · refine tree_all_split_at (125/1024 : ℚ) (by norm_num) ?_ ?_
                    · exact cover8_tree0006_checked hidentity
                    · exact cover8_tree0007_checked hidentity
                  · refine tree_all_split_at (127/1024 : ℚ) (by norm_num) ?_ ?_
                    · refine tree_all_split_at (253/2048 : ℚ) (by norm_num) ?_ ?_
                      · exact cover8_tree0008_checked hidentity
                      · exact cover8_tree0009_checked hidentity
                    · refine tree_all_split_at (255/2048 : ℚ) (by norm_num) ?_ ?_
                      · exact cover8_tree0010_checked hidentity
                      · refine tree_all_split_at (511/4096 : ℚ) (by norm_num) ?_ ?_
                        · exact cover8_tree0011_checked hidentity
                        · exact cover8_tree0012_checked hidentity
      · refine tree_all_split_at (3/16 : ℚ) (by norm_num) ?_ ?_
        · refine tree_all_split_at (5/32 : ℚ) (by norm_num) ?_ ?_
          · refine tree_all_split_at (9/64 : ℚ) (by norm_num) ?_ ?_
            · refine tree_all_split_at (17/128 : ℚ) (by norm_num) ?_ ?_
              · refine tree_all_split_at (33/256 : ℚ) (by norm_num) ?_ ?_
                · refine tree_all_split_at (65/512 : ℚ) (by norm_num) ?_ ?_
                  · refine tree_all_split_at (129/1024 : ℚ) (by norm_num) ?_ ?_
                    · refine tree_all_split_at (257/2048 : ℚ) (by norm_num) ?_ ?_
                      · refine tree_all_split_at (513/4096 : ℚ) (by norm_num) ?_ ?_
                        · exact cover8_tree0013_checked hidentity
                        · exact cover8_tree0014_checked hidentity
                      · refine tree_all_split_at (515/4096 : ℚ) (by norm_num) ?_ ?_
                        · refine tree_all_split_at (1029/8192 : ℚ) (by norm_num) ?_ ?_
                          · exact cover8_tree0015_checked hidentity
                          · exact cover8_tree0016_checked hidentity
                        · refine tree_all_split_at (1031/8192 : ℚ) (by norm_num) ?_ ?_
                          · exact cover8_tree0017_checked hidentity
                          · exact cover8_tree0018_checked hidentity
                    · refine tree_all_split_at (259/2048 : ℚ) (by norm_num) ?_ ?_
                      · refine tree_all_split_at (517/4096 : ℚ) (by norm_num) ?_ ?_
                        · refine tree_all_split_at (1033/8192 : ℚ) (by norm_num) ?_ ?_
                          · exact cover8_tree0019_checked hidentity
                          · exact cover8_tree0020_checked hidentity
                        · refine tree_all_split_at (1035/8192 : ℚ) (by norm_num) ?_ ?_
                          · exact cover8_tree0021_checked hidentity
                          · refine tree_all_split_at (2071/16384 : ℚ) (by norm_num) ?_ ?_
                            · exact cover8_tree0022_checked hidentity
                            · exact cover8_tree0023_checked hidentity
                      · refine tree_all_split_at (519/4096 : ℚ) (by norm_num) ?_ ?_
                        · refine tree_all_split_at (1037/8192 : ℚ) (by norm_num) ?_ ?_
                          · refine tree_all_split_at (2073/16384 : ℚ) (by norm_num) ?_ ?_
                            · exact cover8_tree0024_checked hidentity
                            · exact cover8_tree0025_checked hidentity
                          · refine tree_all_split_at (2075/16384 : ℚ) (by norm_num) ?_ ?_
                            · exact cover8_tree0026_checked hidentity
                            · exact cover8_tree0027_checked hidentity
                        · refine tree_all_split_at (1039/8192 : ℚ) (by norm_num) ?_ ?_
                          · refine tree_all_split_at (2077/16384 : ℚ) (by norm_num) ?_ ?_
                            · exact cover8_tree0028_checked hidentity
                            · exact cover8_tree0029_checked hidentity
                          · refine tree_all_split_at (2079/16384 : ℚ) (by norm_num) ?_ ?_
                            · exact cover8_tree0030_checked hidentity
                            · exact cover8_tree0031_checked hidentity
                  · refine tree_all_split_at (131/1024 : ℚ) (by norm_num) ?_ ?_
                    · refine tree_all_split_at (261/2048 : ℚ) (by norm_num) ?_ ?_
                      · refine tree_all_split_at (521/4096 : ℚ) (by norm_num) ?_ ?_
                        · refine tree_all_split_at (1041/8192 : ℚ) (by norm_num) ?_ ?_
                          · refine tree_all_split_at (2081/16384 : ℚ) (by norm_num) ?_ ?_
                            · exact cover8_tree0032_checked hidentity
                            · refine tree_all_split_at (4163/32768 : ℚ) (by norm_num) ?_ ?_
                              · exact cover8_tree0033_checked hidentity
                              · exact cover8_tree0034_checked hidentity
                          · refine tree_all_split_at (2083/16384 : ℚ) (by norm_num) ?_ ?_
                            · refine tree_all_split_at (4165/32768 : ℚ) (by norm_num) ?_ ?_
                              · exact cover8_tree0035_checked hidentity
                              · exact cover8_tree0036_checked hidentity
                            · refine tree_all_split_at (4167/32768 : ℚ) (by norm_num) ?_ ?_
                              · exact cover8_tree0037_checked hidentity
                              · exact cover8_tree0038_checked hidentity
                        · refine tree_all_split_at (1043/8192 : ℚ) (by norm_num) ?_ ?_
                          · refine tree_all_split_at (2085/16384 : ℚ) (by norm_num) ?_ ?_
                            · refine tree_all_split_at (4169/32768 : ℚ) (by norm_num) ?_ ?_
                              · exact cover8_tree0039_checked hidentity
                              · exact cover8_tree0040_checked hidentity
                            · refine tree_all_split_at (4171/32768 : ℚ) (by norm_num) ?_ ?_
                              · exact cover8_tree0041_checked hidentity
                              · exact cover8_tree0042_checked hidentity
                          · refine tree_all_split_at (2087/16384 : ℚ) (by norm_num) ?_ ?_
                            · refine tree_all_split_at (4173/32768 : ℚ) (by norm_num) ?_ ?_
                              · exact cover8_tree0043_checked hidentity
                              · exact cover8_tree0044_checked hidentity
                            · refine tree_all_split_at (4175/32768 : ℚ) (by norm_num) ?_ ?_
                              · exact cover8_tree0045_checked hidentity
                              · exact cover8_tree0046_checked hidentity
                      · refine tree_all_split_at (523/4096 : ℚ) (by norm_num) ?_ ?_
                        · refine tree_all_split_at (1045/8192 : ℚ) (by norm_num) ?_ ?_
                          · refine tree_all_split_at (2089/16384 : ℚ) (by norm_num) ?_ ?_
                            · refine tree_all_split_at (4177/32768 : ℚ) (by norm_num) ?_ ?_
                              · exact cover8_tree0047_checked hidentity
                              · exact cover8_tree0048_checked hidentity
                            · refine tree_all_split_at (4179/32768 : ℚ) (by norm_num) ?_ ?_
                              · exact cover8_tree0049_checked hidentity
                              · exact cover8_tree0050_checked hidentity
                          · refine tree_all_split_at (2091/16384 : ℚ) (by norm_num) ?_ ?_
                            · refine tree_all_split_at (4181/32768 : ℚ) (by norm_num) ?_ ?_
                              · exact cover8_tree0051_checked hidentity
                              · exact cover8_tree0052_checked hidentity
                            · refine tree_all_split_at (4183/32768 : ℚ) (by norm_num) ?_ ?_
                              · exact cover8_tree0053_checked hidentity
                              · exact cover8_tree0054_checked hidentity
                        · refine tree_all_split_at (1047/8192 : ℚ) (by norm_num) ?_ ?_
                          · refine tree_all_split_at (2093/16384 : ℚ) (by norm_num) ?_ ?_
                            · refine tree_all_split_at (4185/32768 : ℚ) (by norm_num) ?_ ?_
                              · exact cover8_tree0055_checked hidentity
                              · exact cover8_tree0056_checked hidentity
                            · refine tree_all_split_at (4187/32768 : ℚ) (by norm_num) ?_ ?_
                              · exact cover8_tree0057_checked hidentity
                              · exact cover8_tree0058_checked hidentity
                          · refine tree_all_split_at (2095/16384 : ℚ) (by norm_num) ?_ ?_
                            · refine tree_all_split_at (4189/32768 : ℚ) (by norm_num) ?_ ?_
                              · exact cover8_tree0059_checked hidentity
                              · exact cover8_tree0060_checked hidentity
                            · refine tree_all_split_at (4191/32768 : ℚ) (by norm_num) ?_ ?_
                              · exact cover8_tree0061_checked hidentity
                              · exact cover8_tree0062_checked hidentity
                    · refine tree_all_split_at (263/2048 : ℚ) (by norm_num) ?_ ?_
                      · refine tree_all_split_at (525/4096 : ℚ) (by norm_num) ?_ ?_
                        · refine tree_all_split_at (1049/8192 : ℚ) (by norm_num) ?_ ?_
                          · refine tree_all_split_at (2097/16384 : ℚ) (by norm_num) ?_ ?_
                            · refine tree_all_split_at (4193/32768 : ℚ) (by norm_num) ?_ ?_
                              · exact cover8_tree0063_checked hidentity
                              · exact cover8_tree0064_checked hidentity
                            · refine tree_all_split_at (4195/32768 : ℚ) (by norm_num) ?_ ?_
                              · exact cover8_tree0065_checked hidentity
                              · exact cover8_tree0066_checked hidentity
                          · refine tree_all_split_at (2099/16384 : ℚ) (by norm_num) ?_ ?_
                            · refine tree_all_split_at (4197/32768 : ℚ) (by norm_num) ?_ ?_
                              · exact cover8_tree0067_checked hidentity
                              · exact cover8_tree0068_checked hidentity
                            · refine tree_all_split_at (4199/32768 : ℚ) (by norm_num) ?_ ?_
                              · exact cover8_tree0069_checked hidentity
                              · exact cover8_tree0070_checked hidentity
                        · refine tree_all_split_at (1051/8192 : ℚ) (by norm_num) ?_ ?_
                          · refine tree_all_split_at (2101/16384 : ℚ) (by norm_num) ?_ ?_
                            · refine tree_all_split_at (4201/32768 : ℚ) (by norm_num) ?_ ?_
                              · exact cover8_tree0071_checked hidentity
                              · exact cover8_tree0072_checked hidentity
                            · refine tree_all_split_at (4203/32768 : ℚ) (by norm_num) ?_ ?_
                              · exact cover8_tree0073_checked hidentity
                              · exact cover8_tree0074_checked hidentity
                          · refine tree_all_split_at (2103/16384 : ℚ) (by norm_num) ?_ ?_
                            · exact cover8_tree0075_checked hidentity
                            · exact cover8_tree0076_checked hidentity
                      · refine tree_all_split_at (527/4096 : ℚ) (by norm_num) ?_ ?_
                        · refine tree_all_split_at (1053/8192 : ℚ) (by norm_num) ?_ ?_
                          · refine tree_all_split_at (2105/16384 : ℚ) (by norm_num) ?_ ?_
                            · exact cover8_tree0077_checked hidentity
                            · exact cover8_tree0078_checked hidentity
                          · refine tree_all_split_at (2107/16384 : ℚ) (by norm_num) ?_ ?_
                            · exact cover8_tree0079_checked hidentity
                            · exact cover8_tree0080_checked hidentity
                        · refine tree_all_split_at (1055/8192 : ℚ) (by norm_num) ?_ ?_
                          · refine tree_all_split_at (2109/16384 : ℚ) (by norm_num) ?_ ?_
                            · exact cover8_tree0081_checked hidentity
                            · exact cover8_tree0082_checked hidentity
                          · refine tree_all_split_at (2111/16384 : ℚ) (by norm_num) ?_ ?_
                            · exact cover8_tree0083_checked hidentity
                            · exact cover8_tree0084_checked hidentity
                · refine tree_all_split_at (67/512 : ℚ) (by norm_num) ?_ ?_
                  · refine tree_all_split_at (133/1024 : ℚ) (by norm_num) ?_ ?_
                    · refine tree_all_split_at (265/2048 : ℚ) (by norm_num) ?_ ?_
                      · refine tree_all_split_at (529/4096 : ℚ) (by norm_num) ?_ ?_
                        · refine tree_all_split_at (1057/8192 : ℚ) (by norm_num) ?_ ?_
                          · refine tree_all_split_at (2113/16384 : ℚ) (by norm_num) ?_ ?_
                            · exact cover8_tree0085_checked hidentity
                            · exact cover8_tree0086_checked hidentity
                          · exact cover8_tree0087_checked hidentity
                        · refine tree_all_split_at (1059/8192 : ℚ) (by norm_num) ?_ ?_
                          · exact cover8_tree0088_checked hidentity
                          · exact cover8_tree0089_checked hidentity
                      · refine tree_all_split_at (531/4096 : ℚ) (by norm_num) ?_ ?_
                        · refine tree_all_split_at (1061/8192 : ℚ) (by norm_num) ?_ ?_
                          · exact cover8_tree0090_checked hidentity
                          · exact cover8_tree0091_checked hidentity
                        · refine tree_all_split_at (1063/8192 : ℚ) (by norm_num) ?_ ?_
                          · exact cover8_tree0092_checked hidentity
                          · exact cover8_tree0093_checked hidentity
                    · refine tree_all_split_at (267/2048 : ℚ) (by norm_num) ?_ ?_
                      · refine tree_all_split_at (533/4096 : ℚ) (by norm_num) ?_ ?_
                        · exact cover8_tree0094_checked hidentity
                        · exact cover8_tree0095_checked hidentity
                      · refine tree_all_split_at (535/4096 : ℚ) (by norm_num) ?_ ?_
                        · exact cover8_tree0096_checked hidentity
                        · exact cover8_tree0097_checked hidentity
                  · refine tree_all_split_at (135/1024 : ℚ) (by norm_num) ?_ ?_
                    · refine tree_all_split_at (269/2048 : ℚ) (by norm_num) ?_ ?_
                      · exact cover8_tree0098_checked hidentity
                      · exact cover8_tree0099_checked hidentity
                    · exact cover8_tree0100_checked hidentity
              · refine tree_all_split_at (35/256 : ℚ) (by norm_num) ?_ ?_
                · refine tree_all_split_at (69/512 : ℚ) (by norm_num) ?_ ?_
                  · refine tree_all_split_at (137/1024 : ℚ) (by norm_num) ?_ ?_
                    · exact cover8_tree0101_checked hidentity
                    · exact cover8_tree0102_checked hidentity
                  · exact cover8_tree0103_checked hidentity
                · exact cover8_tree0104_checked hidentity
            · exact cover8_tree0105_checked hidentity
          · exact cover8_tree0106_checked hidentity
        · exact cover8_tree0107_checked hidentity
    · exact cover8_tree0108_checked hidentity
  · simpa only [div_one] using cover8_tree0109_checked hidentity

theorem cover8_best_bound_lower
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus)))
    (hdlmf : ∀ modulus ∈ Ioo (0 : ℝ) 1,
      Real.log ((1 + Real.sqrt (complement modulus))^2 / modulus) < mu modulus ∧
      mu modulus < Real.log (2 * (1 + complement modulus) / modulus)) :
    (20549/10000 : ℝ) < bestBound 8 := by
  have hcover := dyadic_unit_cover cover8_tree
  have hleaves := (tree_boxes_all (fun box => BoxEndpointBound 8 box ∧ (20549/10000 : ℝ) < (box.lower : ℝ)) cover8_tree 0 1).mpr (cover8_tree_checked hidentity)
  refine finite_box_soundness_from_dlmf hdlmf 8 (by omega)
    (treeBoxes cover8_tree 0 1) hcover.1 hcover.2.2 hcover.2.1
    (fun box hbox => (hleaves box hbox).1) (20549/10000 : ℝ)
    (fun box hbox => (hleaves box hbox).2) ?_
  have hexp := exp_lower_eight (6/7 : ℝ) (by norm_num)
  norm_num [Finset.sum_range_succ] at hexp
  linarith

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_best_bound_lower
#print axioms SmaleRate.Proofs.cover8_best_bound_lower
