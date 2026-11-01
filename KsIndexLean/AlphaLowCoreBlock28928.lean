module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate28928

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache28928
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (12543) (12799)) n =
      blockLinearNumerator (12543) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (12543) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 28928 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+28928 = 12543 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (12543) (12799)) n =
      blockLinearRadius (12543) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (12543) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 28928 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+28928 = 12543 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (12543) (12799)) (-2) = 122752405599664047202113460069529517441961894748 ∧
    lowLinearRadius (Finset.Ico (12543) (12799)) (-2) = 182965523154064534543845585588041385829 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (12543) (12799)) (-1) = -122762093315955859705225915122160883167941440177 ∧
    lowLinearRadius (Finset.Ico (12543) (12799)) (-1) = 182979962965131429991479093397370181640 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (12543) (12799)) (1) = -122781473336792857823547447867814643762433629189 ∧
    lowLinearRadius (Finset.Ico (12543) (12799)) (1) = 183008849426198090171179768297681241731 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (12543) (12799)) (2) = 122791165642062481363199937611500367854765650878 ∧
    lowLinearRadius (Finset.Ico (12543) (12799)) (2) = 183023296077277654037499522574699035258 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache28928
