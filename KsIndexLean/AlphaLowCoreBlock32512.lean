module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate32512

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache32512
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (16127) (16383)) n =
      blockLinearNumerator (16127) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (16127) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 32512 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+32512 = 16127 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (16127) (16383)) n =
      blockLinearRadius (16127) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (16127) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 32512 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+32512 = 16127 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (16127) (16383)) (-2) = 85011773311993939457093255176269037932671719729 ∧
    lowLinearRadius (Finset.Ico (16127) (16383)) (-2) = 124909127625010542223776060819524915213 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (16127) (16383)) (-1) = -85017003142264311262819649449320041396747101308 ∧
    lowLinearRadius (Finset.Ico (16127) (16383)) (-1) = 124916811905536272741369536979108545030 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (16127) (16383)) (1) = -85027464733482750285314115196687301760086130373 ∧
    lowLinearRadius (Finset.Ico (16127) (16383)) (1) = 124932183303369408634306740145109934204 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (16127) (16383)) (2) = 85032696494668417487554314418928879885489906172 ∧
    lowLinearRadius (Finset.Ico (16127) (16383)) (2) = 124939870421025924629479478700115143052 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache32512
