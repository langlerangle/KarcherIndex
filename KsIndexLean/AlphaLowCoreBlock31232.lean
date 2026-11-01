module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate31232

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache31232
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (14847) (15103)) n =
      blockLinearNumerator (14847) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (14847) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 31232 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+31232 = 14847 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (14847) (15103)) n =
      blockLinearRadius (14847) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (14847) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 31232 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+31232 = 14847 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (14847) (15103)) (-2) = 95940951415049412676991220876250828961296416414 ∧
    lowLinearRadius (Finset.Ico (14847) (15103)) (-2) = 141634732732910825315297823830359112650 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (14847) (15103)) (-1) = -95947358114653380833661069369584904038735049171 ∧
    lowLinearRadius (Finset.Ico (14847) (15103)) (-1) = 141644190763547693008993308306957266155 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (14847) (15103)) (1) = -95960174081208109864003097238208754322751581418 ∧
    lowLinearRadius (Finset.Ico (14847) (15103)) (1) = 141663110614928684157731848652602889916 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (14847) (15103)) (2) = 95966583348501838296489816784987437179106695864 ∧
    lowLinearRadius (Finset.Ico (14847) (15103)) (2) = 141672572436179122403879602730993900558 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache31232
