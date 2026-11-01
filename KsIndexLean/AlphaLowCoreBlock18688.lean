module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate18688

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache18688
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (2303) (2559)) n =
      blockLinearNumerator (2303) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (2303) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 18688 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+18688 = 2303 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (2303) (2559)) n =
      blockLinearRadius (2303) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (2303) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 18688 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+18688 = 2303 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (2303) (2559)) (-2) = 1411862294038105357317823556031800145089387746317 ∧
    lowLinearRadius (Finset.Ico (2303) (2559)) (-2) = 2312025484581141021499456952104421253031 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (2303) (2559)) (-1) = -1412444163469643406701692725576926393816975061705 ∧
    lowLinearRadius (Finset.Ico (2303) (2559)) (-1) = 2312978386930279895881906052799171221415 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (2303) (2559)) (1) = -1413609343684524021811391575629816192386651277319 ∧
    lowLinearRadius (Finset.Ico (2303) (2559)) (1) = 2314886552190552522659864942749430488294 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (2303) (2559)) (2) = 1414192655659585586197381861898985925199964840396 ∧
    lowLinearRadius (Finset.Ico (2303) (2559)) (2) = 2315841817053515350081610898287908160363 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache18688
