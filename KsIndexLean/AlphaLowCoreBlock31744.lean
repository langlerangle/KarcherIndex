module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate31744

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache31744
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (15359) (15615)) n =
      blockLinearNumerator (15359) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (15359) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 31744 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+31744 = 15359 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (15359) (15615)) n =
      blockLinearRadius (15359) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (15359) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 31744 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+31744 = 15359 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (15359) (15615)) (-2) = 91300463863586815928628382227776443354780796752 ∧
    lowLinearRadius (Finset.Ico (15359) (15615)) (-2) = 134523547843140127762646494211532096229 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (15359) (15615)) (-1) = -91306359112036965449062417854381608062934180246 ∧
    lowLinearRadius (Finset.Ico (15359) (15615)) (-1) = 134532234006854565391352641009929313872 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (15359) (15615)) (1) = -91318151893212704144166910361064492467548632702 ∧
    lowLinearRadius (Finset.Ico (15359) (15615)) (1) = 134549609699979833718260864148919941920 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (15359) (15615)) (2) = 91324049426233354116022037466002386347048273599 ∧
    lowLinearRadius (Finset.Ico (15359) (15615)) (2) = 134558299229825413372413923081543807038 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache31744
