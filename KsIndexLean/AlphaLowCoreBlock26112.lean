module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate26112

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache26112
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (9727) (9983)) n =
      blockLinearNumerator (9727) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (9727) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 26112 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+26112 = 9727 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (9727) (9983)) n =
      blockLinearRadius (9727) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (9727) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 26112 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+26112 = 9727 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (9727) (9983)) (-2) = 177883051643344013151341405343044367622421535569 ∧
    lowLinearRadius (Finset.Ico (9727) (9983)) (-2) = 268993726420388946322917607134588796878 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (9727) (9983)) (-1) = -177901102355707138755837316552080400236627458895 ∧
    lowLinearRadius (Finset.Ico (9727) (9983)) (-1) = 269021022691710720993427154221920203196 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (9727) (9983)) (1) = -177937214773476892879934770696532456989110781306 ∧
    lowLinearRadius (Finset.Ico (9727) (9983)) (1) = 269075631858078577250545544018619944361 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (9727) (9983)) (2) = 177955276481115493722395299684884851525977564872 ∧
    lowLinearRadius (Finset.Ico (9727) (9983)) (2) = 269102944756499867186141543168206850358 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache26112
