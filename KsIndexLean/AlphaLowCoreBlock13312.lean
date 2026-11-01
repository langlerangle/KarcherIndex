module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate13312

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache13312
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-3073) (-2817)) n =
      blockLinearNumerator (-3073) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-3073) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 13312 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+13312 = -3073 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-3073) (-2817)) n =
      blockLinearRadius (-3073) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-3073) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 13312 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+13312 = -3073 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-3073) (-2817)) (-2) = -291539927452599597795463568939046282466841928346 ∧
    lowLinearRadius (Finset.Ico (-3073) (-2817)) (-2) = 1722739559667274323157975658913095926073 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-3073) (-2817)) (-1) = 291440758089816612857646001148594293836142165042 ∧
    lowLinearRadius (Finset.Ico (-3073) (-2817)) (-1) = 1722153452521433379891715113246230408361 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-3073) (-2817)) (1) = 291242621752987843423501396017446313083409668166 ∧
    lowLinearRadius (Finset.Ico (-3073) (-2817)) (1) = 1720982434594510686126297391308426927693 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-3073) (-2817)) (2) = -291143654641221396552916845070189448082309571716 ∧
    lowLinearRadius (Finset.Ico (-3073) (-2817)) (2) = 1720397522999186020538048227351983116407 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache13312
