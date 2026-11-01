module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate3328

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache3328
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-13057) (-12801)) n =
      blockLinearNumerator (-13057) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-13057) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 3328 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+3328 = -13057 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-13057) (-12801)) n =
      blockLinearRadius (-13057) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-13057) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 3328 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+3328 = -13057 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-13057) (-12801)) (-2) = -43382409032258664848618349401771192434186652676 ∧
    lowLinearRadius (Finset.Ico (-13057) (-12801)) (-2) = 177449034248308917685417464078983438529 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-13057) (-12801)) (-1) = 43379053084714146248518807908126622597453128649 ∧
    lowLinearRadius (Finset.Ico (-13057) (-12801)) (-1) = 177435307165849021571267534723545324112 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-13057) (-12801)) (1) = 43372342747077981101503143954050051700861892522 ∧
    lowLinearRadius (Finset.Ico (-13057) (-12801)) (1) = 177407859371540347816349993420962018024 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-13057) (-12801)) (2) = -43368988356745413917693407706982270694746692689 ∧
    lowLinearRadius (Finset.Ico (-13057) (-12801)) (2) = 177394138658706100452067350916702364099 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache3328
