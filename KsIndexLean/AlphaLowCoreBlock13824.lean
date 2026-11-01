module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate13824

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache13824
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-2561) (-2305)) n =
      blockLinearNumerator (-2561) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-2561) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 13824 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+13824 = -2561 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-2561) (-2305)) n =
      blockLinearRadius (-2561) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-2561) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 13824 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+13824 = -2561 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-2561) (-2305)) (-2) = -370182221244159574987319154961360026467396646838 ∧
    lowLinearRadius (Finset.Ico (-2561) (-2305)) (-2) = 2312587693720398638366428276731379433134 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-2561) (-2305)) (-1) = 370029692236838318598633787384672416589686530615 ∧
    lowLinearRadius (Finset.Ico (-2561) (-2305)) (-1) = 2311634559444588608204831344904732253036 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-2561) (-2305)) (1) = 369725011345641189852052678889429675286688587914 ∧
    lowLinearRadius (Finset.Ico (-2561) (-2305)) (1) = 2309730648133476799313194601864985109830 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-2561) (-2305)) (2) = -369572859150798510202628110697686089762685897105 ∧
    lowLinearRadius (Finset.Ico (-2561) (-2305)) (2) = 2308779869153922082935711490460639224022 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache13824
