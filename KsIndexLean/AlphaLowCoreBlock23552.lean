module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate23552

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache23552
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (7167) (7423)) n =
      blockLinearNumerator (7167) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (7167) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 23552 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+23552 = 7167 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (7167) (7423)) n =
      blockLinearRadius (7167) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (7167) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 23552 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+23552 = 7167 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (7167) (7423)) (-2) = 277390049268409798331876625433876593105094240616 ∧
    lowLinearRadius (Finset.Ico (7167) (7423)) (-2) = 426757089749317147992918821998392501148 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (7167) (7423)) (-1) = -277428078404748021882359425627901110650444997796 ∧
    lowLinearRadius (Finset.Ico (7167) (7423)) (-1) = 426815596890430299011259583622680277202 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (7167) (7423)) (1) = -277504167971128979578535309242384328709220314734 ∧
    lowLinearRadius (Finset.Ico (7167) (7423)) (1) = 426932659317739655008920059619651766245 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (7167) (7423)) (2) = 277542228409757506236686697208345520266281605987 ∧
    lowLinearRadius (Finset.Ico (7167) (7423)) (2) = 426991214617145102064348523814246702826 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache23552
