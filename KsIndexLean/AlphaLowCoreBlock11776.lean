module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate11776

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache11776
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-4609) (-4353)) n =
      blockLinearNumerator (-4609) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-4609) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 11776 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+11776 = -4609 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-4609) (-4353)) n =
      blockLinearRadius (-4609) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-4609) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 11776 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+11776 = -4609 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-4609) (-4353)) (-2) = -171362386611266577023576856739908693629608280680 ∧
    lowLinearRadius (Finset.Ico (-4609) (-4353)) (-2) = 902871364660280829878048538349021978425 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-4609) (-4353)) (-1) = 171324112384286796894909908573818349266205178605 ∧
    lowLinearRadius (Finset.Ico (-4609) (-4353)) (-1) = 902669691668322852373224990731904279190 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-4609) (-4353)) (1) = 171247615213246983703512668066007345381847432222 ∧
    lowLinearRadius (Finset.Ico (-4609) (-4353)) (1) = 902266615921503062526737486113472012702 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-4609) (-4353)) (2) = -171209392246281501762967136165189541655344317558 ∧
    lowLinearRadius (Finset.Ico (-4609) (-4353)) (2) = 902065213045931623299240488315462619459 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache11776
