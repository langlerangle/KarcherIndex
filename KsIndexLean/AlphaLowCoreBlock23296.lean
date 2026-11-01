module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate23296

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache23296
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (6911) (7167)) n =
      blockLinearNumerator (6911) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (6911) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 23296 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+23296 = 6911 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (6911) (7167)) n =
      blockLinearRadius (6911) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (6911) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 23296 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+23296 = 6911 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (6911) (7167)) (-2) = 292427870202575623007459021896655271653706696062 ∧
    lowLinearRadius (Finset.Ico (6911) (7167)) (-2) = 450812227391277768509753140624921710718 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (6911) (7167)) (-1) = -292469419596796985450069942701700903469926003070 ∧
    lowLinearRadius (Finset.Ico (6911) (7167)) (-1) = 450876281111307735406059382611580014986 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (6911) (7167)) (1) = -292552553820301776315754184978313071039880465240 ∧
    lowLinearRadius (Finset.Ico (6911) (7167)) (1) = 451004443179404584318702947211699440442 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (6911) (7167)) (2) = 292594138659661248999446028505165764820586296681 ∧
    lowLinearRadius (Finset.Ico (6911) (7167)) (2) = 451068551543005176511068711510898672928 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache23296
