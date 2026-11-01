module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate9216

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache9216
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-7169) (-6913)) n =
      blockLinearNumerator (-7169) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-7169) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 9216 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+9216 = -7169 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-7169) (-6913)) n =
      blockLinearRadius (-7169) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-7169) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 9216 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+9216 = -7169 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-7169) (-6913)) (-2) = -95865129489742377150528148648541475900510084711 ∧
    lowLinearRadius (Finset.Ico (-7169) (-6913)) (-2) = 450850456682414324953746155377900636818 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-7169) (-6913)) (-1) = 95851508841097741241219064628008063958837670483 ∧
    lowLinearRadius (Finset.Ico (-7169) (-6913)) (-1) = 450786397529978141970115529620510138883 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-7169) (-6913)) (1) = 95824279153230722532582442644369928143778366579 ∧
    lowLinearRadius (Finset.Ico (-7169) (-6913)) (1) = 450658333826728226741803224451094986467 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-7169) (-6913)) (2) = -95810670110710053910637638383856076015925102677 ∧
    lowLinearRadius (Finset.Ico (-7169) (-6913)) (2) = 450594329260401531197369909339098698087 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache9216
