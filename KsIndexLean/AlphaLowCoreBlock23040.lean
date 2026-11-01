module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate23040

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache23040
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (6655) (6911)) n =
      blockLinearNumerator (6655) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (6655) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 23040 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+23040 = 6655 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (6655) (6911)) n =
      blockLinearRadius (6655) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (6655) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 23040 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+23040 = 6655 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (6655) (6911)) (-2) = 308886429925562180917808238023182431167783759847 ∧
    lowLinearRadius (Finset.Ico (6655) (6911)) (-2) = 477194364463131017763510158662124880961 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (6655) (6911)) (-1) = -308931974926239212837613419223991695137537397826 ∧
    lowLinearRadius (Finset.Ico (6655) (6911)) (-1) = 477264726780450478901082389027845868652 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (6655) (6911)) (1) = -309023105237659136400960964320914302953924564212 ∧
    lowLinearRadius (Finset.Ico (6655) (6911)) (1) = 477405513690395877648370592638750205862 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (6655) (6911)) (2) = 309068690560297472826404608697690335541538218922 ∧
    lowLinearRadius (Finset.Ico (6655) (6911)) (2) = 477475938301399296794120302359468323069 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache23040
