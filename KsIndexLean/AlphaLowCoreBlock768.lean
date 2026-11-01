module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate768

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache768
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-15617) (-15361)) n =
      blockLinearNumerator (-15617) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-15617) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 768 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+768 = -15617 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-15617) (-15361)) n =
      blockLinearRadius (-15617) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-15617) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 768 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+768 = -15617 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-15617) (-15361)) (-2) = -34196562737458261086094314828006363166728476394 ∧
    lowLinearRadius (Finset.Ico (-15617) (-15361)) (-2) = 134528779127982716312426787851982418276 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-15617) (-15361)) (-1) = 34194354681632345531521704973995255983359392136 ∧
    lowLinearRadius (Finset.Ico (-15617) (-15361)) (-1) = 134520092626477462757905481657369474103 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-15617) (-15361)) (1) = 34189939425328227051029060832217240501676179735 ∧
    lowLinearRadius (Finset.Ico (-15617) (-15361)) (1) = 134502722988424987120108948926646561035 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-15617) (-15361)) (2) = -34187732224739581699179246626643755393176971426 ∧
    lowLinearRadius (Finset.Ico (-15617) (-15361)) (2) = 134494039851443279829605485013389476969 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache768
