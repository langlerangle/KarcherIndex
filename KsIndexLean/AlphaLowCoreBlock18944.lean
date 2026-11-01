module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate18944

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache18944
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (2559) (2815)) n =
      blockLinearNumerator (2559) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (2559) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 18944 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+18944 = 2559 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (2559) (2815)) n =
      blockLinearRadius (2559) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (2559) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 18944 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+18944 = 2559 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (2559) (2815)) (-2) = 1216886659500135382054453201652377642177845002331 ∧
    lowLinearRadius (Finset.Ico (2559) (2815)) (-2) = 1981507384898462982163613731558894720412 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (2559) (2815)) (-1) = -1217340221296405691322102119778010347941032303727 ∧
    lowLinearRadius (Finset.Ico (2559) (2815)) (-1) = 1982245970000564775719710259134821131571 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (2559) (2815)) (1) = -1218248360732461555470179930136337631444684899913 ∧
    lowLinearRadius (Finset.Ico (2559) (2815)) (1) = 1983724794486177402700889418615755903914 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (2559) (2815)) (2) = 1218702939131500253280511195302458287075464607157 ∧
    lowLinearRadius (Finset.Ico (2559) (2815)) (2) = 1984465035106169783205829569030899042976 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache18944
