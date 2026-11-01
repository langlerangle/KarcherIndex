module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate3584

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache3584
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-12801) (-12545)) n =
      blockLinearNumerator (-12801) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-12801) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 3584 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+3584 = -12801 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-12801) (-12545)) n =
      blockLinearRadius (-12801) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-12801) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 3584 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+3584 = -12801 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-12801) (-12545)) (-2) = -44537649095881021493795250640778558572681156233 ∧
    lowLinearRadius (Finset.Ico (-12801) (-12545)) (-2) = 182974199267268340205122358659834285052 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-12801) (-12545)) (-1) = 44534134168967284131512218258669426650276187313 ∧
    lowLinearRadius (Finset.Ico (-12801) (-12545)) (-1) = 182959758771451417564628981458018524253 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-12801) (-12545)) (1) = 44527105979329324193636994867461792444834912840 ∧
    lowLinearRadius (Finset.Ico (-12801) (-12545)) (1) = 182930884616915912881344887319934622254 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-12801) (-12545)) (2) = -44523592716342469097059760156642740683157987239 ∧
    lowLinearRadius (Finset.Ico (-12801) (-12545)) (2) = 182916450957118332474453317591398192175 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache3584
