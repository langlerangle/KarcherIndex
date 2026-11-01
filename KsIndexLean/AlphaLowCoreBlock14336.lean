module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate14336

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache14336
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-2049) (-1793)) n =
      blockLinearNumerator (-2049) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-2049) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 14336 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+14336 = -2049 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-2049) (-1793)) n =
      blockLinearRadius (-2049) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-2049) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 14336 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+14336 = -2049 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-2049) (-1793)) (-2) = -495999644855917609566989455960537686709861876765 ∧
    lowLinearRadius (Finset.Ico (-2049) (-1793)) (-2) = 3330870844192384554960400335196504052788 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-2049) (-1793)) (-1) = 495740456127308667766494399239145986102517755572 ∧
    lowLinearRadius (Finset.Ico (-2049) (-1793)) (-1) = 3329129461733964338897898737599128326934 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-2049) (-1793)) (1) = 495222891671740893070829784549676264970596472449 ∧
    lowLinearRadius (Finset.Ico (-2049) (-1793)) (1) = 3325652161568772168492987263332723842279 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-2049) (-1793)) (2) = -494964515093920633688249083020162233689849385345 ∧
    lowLinearRadius (Finset.Ico (-2049) (-1793)) (2) = 3323916238140131850370335721554598112277 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache14336
