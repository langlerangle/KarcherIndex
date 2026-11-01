module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate15616

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache15616
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-769) (-513)) n =
      blockLinearNumerator (-769) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-769) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 15616 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+15616 = -769 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-769) (-513)) n =
      blockLinearRadius (-769) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-769) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 15616 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+15616 = -769 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-769) (-513)) (-2) = -1834447383213263507210508549804484161674678951317 ∧
    lowLinearRadius (Finset.Ico (-769) (-513)) (-2) = 18540831311519088654916323947771541790510 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-769) (-513)) (-1) = 1831497283950122210914232547905400277730907418774 ∧
    lowLinearRadius (Finset.Ico (-769) (-513)) (-1) = 18510839990758911926664824059093627792834 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-769) (-513)) (1) = 1825625843794608987619505401277367882365382596277 ∧
    lowLinearRadius (Finset.Ico (-769) (-513)) (1) = 18451151385524351865454409658796954575130 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-769) (-513)) (2) = -1822704408379279245052270429924546098470524433129 ∧
    lowLinearRadius (Finset.Ico (-769) (-513)) (2) = 18421453129282555036666744815449791675732 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache15616
