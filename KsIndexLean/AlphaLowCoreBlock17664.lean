module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate17664

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache17664
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (1279) (1535)) n =
      blockLinearNumerator (1279) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (1279) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 17664 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+17664 = 1279 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (1279) (1535)) n =
      blockLinearRadius (1279) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (1279) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 17664 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+17664 = 1279 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (1279) (1535)) (-2) = 3186379696841117194896675951264041078528645311432 ∧
    lowLinearRadius (Finset.Ico (1279) (1535)) (-2) = 5381044894999335657638950461785427555963 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (1279) (1535)) (-1) = -3188658359852952506406655915621949063295001477556 ∧
    lowLinearRadius (Finset.Ico (1279) (1535)) (-1) = 5384893612302022649029128127823269467551 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (1279) (1535)) (1) = -3193225504198426772172123872459961228267641788445 ∧
    lowLinearRadius (Finset.Ico (1279) (1535)) (1) = 5392607632834475592217796161160583126687 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (1279) (1535)) (2) = 3195513999682857572729504322818230366301719258005 ∧
    lowLinearRadius (Finset.Ico (1279) (1535)) (2) = 5396472959972575120861037285368812426361 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache17664
