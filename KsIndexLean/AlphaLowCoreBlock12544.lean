module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate12544

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache12544
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-3841) (-3585)) n =
      blockLinearNumerator (-3841) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-3841) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 12544 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+12544 = -3841 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-3841) (-3585)) n =
      blockLinearRadius (-3841) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-3841) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 12544 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+12544 = -3841 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-3841) (-3585)) (-2) = -217641234903888584422622234582540726103344124395 ∧
    lowLinearRadius (Finset.Ico (-3841) (-3585)) (-2) = 1205706976609547007330689564062098685899 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-3841) (-3585)) (-1) = 217582550395449480017871385814159845108105905750 ∧
    lowLinearRadius (Finset.Ico (-3841) (-3585)) (-1) = 1205381836311565991895803728963285869190 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-3841) (-3585)) (1) = 217465276306690787051920442360193641466716405133 ∧
    lowLinearRadius (Finset.Ico (-3841) (-3585)) (1) = 1204732081719410484868204653610705441950 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-3841) (-3585)) (2) = -217406686675179477364423459405840916749542095839 ∧
    lowLinearRadius (Finset.Ico (-3841) (-3585)) (2) = 1204407467141548390682043612669736875029 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache12544
