module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate19712

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache19712
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (3327) (3583)) n =
      blockLinearNumerator (3327) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (3327) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 19712 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+19712 = 3327 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (3327) (3583)) n =
      blockLinearRadius (3327) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (3327) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 19712 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+19712 = 3327 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (3327) (3583)) (-2) = 838217580536657837747713643147066457189252478401 ∧
    lowLinearRadius (Finset.Ico (3327) (3583)) (-2) = 1345629902215747535649361483791099790281 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (3327) (3583)) (-1) = -838460395799697312434842672828764572257082303594 ∧
    lowLinearRadius (Finset.Ico (3327) (3583)) (-1) = 1346019715008922373949601242430182084985 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (3327) (3583)) (1) = -838946448796867619351528941590683002177946808288 ∧
    lowLinearRadius (Finset.Ico (3327) (3583)) (1) = 1346800018842989705090270214820183594277 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (3327) (3583)) (2) = 839189686776199019213174995257397118837078233377 ∧
    lowLinearRadius (Finset.Ico (3327) (3583)) (2) = 1347190510277544694284532474754120938692 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache19712
