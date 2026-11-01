module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate4352

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache4352
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-12033) (-11777)) n =
      blockLinearNumerator (-12033) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-12033) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 4352 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+4352 = -12033 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-12033) (-11777)) n =
      blockLinearRadius (-12033) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-12033) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 4352 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+4352 = -12033 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-12033) (-11777)) (-2) = -48347226876467331374543277363101649352089122428 ∧
    lowLinearRadius (Finset.Ico (-12033) (-11777)) (-2) = 201381436451176361596930403611515929145 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-12033) (-11777)) (-1) = 48343165087601518839980899135898291797753852519 ∧
    lowLinearRadius (Finset.Ico (-12033) (-11777)) (-1) = 201364517676072653613075505229837158942 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-12033) (-11777)) (1) = 48335043557059826411988191031702743391733063101 ∧
    lowLinearRadius (Finset.Ico (-12033) (-11777)) (1) = 201330688653202031287145330034415492877 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-12033) (-11777)) (2) = -48330983815040026129809831945580629000041556643 ∧
    lowLinearRadius (Finset.Ico (-12033) (-11777)) (2) = 201313778404002543464256100670384341345 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache4352
