module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate12288

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache12288
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-4097) (-3841)) n =
      blockLinearNumerator (-4097) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-4097) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 12288 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+12288 = -4097 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-4097) (-3841)) n =
      blockLinearRadius (-4097) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-4097) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 12288 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+12288 = -4097 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-4097) (-3841)) (-2) = -199987041025698666723400172802651487649498027779 ∧
    lowLinearRadius (Finset.Ico (-4097) (-3841)) (-2) = 1088134496611831567164448929440987576926 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-4097) (-3841)) (-1) = 199936601361428548176254693413108991560976185002 ∧
    lowLinearRadius (Finset.Ico (-4097) (-3841)) (-1) = 1087860027625918285828120905372916460494 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-4097) (-3841)) (1) = 199835798350590834140951680238143720789197081145 ∧
    lowLinearRadius (Finset.Ico (-4097) (-3841)) (1) = 1087311504977779870264247760432638606354 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-4097) (-3841)) (2) = -199785434965528801306940072375084657373753943316 ∧
    lowLinearRadius (Finset.Ico (-4097) (-3841)) (2) = 1087037451106047192625873891100197931885 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache12288
