module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate30976

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache30976
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (14591) (14847)) n =
      blockLinearNumerator (14591) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (14591) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 30976 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+30976 = 14591 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (14591) (14847)) n =
      blockLinearRadius (14591) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (14591) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 30976 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+30976 = 14591 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (14591) (14847)) (-2) = 98411979441336256501086815408879370261927036782 ∧
    lowLinearRadius (Finset.Ico (14591) (14847)) (-2) = 145426880700872219020540076086229372662 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (14591) (14847)) (-1) = -98418665454819560061332345025922169621171421961 ∧
    lowLinearRadius (Finset.Ico (14591) (14847)) (-1) = 145436760875024272913892445729568865723 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (14591) (14847)) (1) = -98432040207672509550770591765288232330456382938 ∧
    lowLinearRadius (Finset.Ico (14591) (14847)) (1) = 145456525251479223716003999177941177478 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (14591) (14847)) (2) = 98438728947412637764458977099341461808941177222 ∧
    lowLinearRadius (Finset.Ico (14591) (14847)) (2) = 145466409454329597850139161517907883379 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache30976
