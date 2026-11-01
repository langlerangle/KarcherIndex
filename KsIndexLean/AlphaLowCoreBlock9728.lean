module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate9728

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache9728
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-6657) (-6401)) n =
      blockLinearNumerator (-6657) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-6657) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 9728 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+9728 = -6657 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-6657) (-6401)) n =
      blockLinearRadius (-6657) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-6657) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 9728 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+9728 = -6657 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-6657) (-6401)) (-2) = -105693591080016979295481497573530589540577126833 ∧
    lowLinearRadius (Finset.Ico (-6657) (-6401)) (-2) = 506276179065258535008616916517843837218 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-6657) (-6401)) (-1) = 105677395517661576673443014477395012254736102834 ∧
    lowLinearRadius (Finset.Ico (-6657) (-6401)) (-1) = 506198599296842748080419487121610057899 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-6657) (-6401)) (1) = 105645019280294498226288108690179719515227845819 ∧
    lowLinearRadius (Finset.Ico (-6657) (-6401)) (1) = 506043511075401156777115155318608031066 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-6657) (-6401)) (2) = -105628838600721337832435811747890360005761253489 ∧
    lowLinearRadius (Finset.Ico (-6657) (-6401)) (2) = 505966002600523621272203246370293274140 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache9728
