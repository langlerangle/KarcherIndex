module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate3840

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache3840
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-12545) (-12289)) n =
      blockLinearNumerator (-12545) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-12545) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 3840 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+3840 = -12545 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-12545) (-12289)) n =
      blockLinearRadius (-12545) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-12545) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 3840 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+3840 = -12545 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-12545) (-12289)) (-2) = -45747619179422446718874938341439505533839875830 ∧
    lowLinearRadius (Finset.Ico (-12545) (-12289)) (-2) = 188789799656268563645175033040332511463 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-12545) (-12289)) (-1) = 45743934307632360252321566740881488707264243480 ∧
    lowLinearRadius (Finset.Ico (-12545) (-12289)) (-1) = 188774592927645397705895000958258302474 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-12545) (-12289)) (1) = 45736566344679130324345626689651851368321414131 ∧
    lowLinearRadius (Finset.Ico (-12545) (-12289)) (1) = 188744186818747469263733861890860741136 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-12545) (-12289)) (2) = -45732883253229184552125584968658866657492748444 ∧
    lowLinearRadius (Finset.Ico (-12545) (-12289)) (2) = 188728987437289112559175939675952217349 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache3840
