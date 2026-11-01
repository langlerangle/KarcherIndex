module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate16384

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache16384
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-1) (255)) n =
      blockLinearNumerator (-1) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-1) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 16384 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+16384 = -1 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-1) (255)) n =
      blockLinearRadius (-1) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-1) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 16384 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+16384 = -1 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-1) (255)) (-2) = 1113936276892723633365242718378353691771579162096736 ∧
    lowLinearRadius (Finset.Ico (-1) (255)) (-2) = 3964724878268744586572288190924307098173629 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-1) (255)) (-1) = -1476622791332450479500476838661911352373516832802150 ∧
    lowLinearRadius (Finset.Ico (-1) (255)) (-1) = 5353959825288333408784875577630795918966141 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-1) (255)) (1) = -326581545579407164192077757145223336408736201007011 ∧
    lowLinearRadius (Finset.Ico (-1) (255)) (1) = 16917452963600087466870801966692043558726323 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-1) (255)) (2) = 134308136028919035207801608424218068406639063140454 ∧
    lowLinearRadius (Finset.Ico (-1) (255)) (2) = 17664159405121424714704942719332519961290832 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache16384
