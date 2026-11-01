module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate20224

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache20224
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (3839) (4095)) n =
      blockLinearNumerator (3839) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (3839) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 20224 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+20224 = 3839 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (3839) (4095)) n =
      blockLinearRadius (3839) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (3839) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 20224 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+20224 = 3839 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (3839) (4095)) (-2) = 683049854985910615486689095871154359435677888518 ∧
    lowLinearRadius (Finset.Ico (3839) (4095)) (-2) = 1087971739944690092129743669285620339123 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (3839) (4095)) (-1) = -683222142789707190396316433937231005091241600939 ∧
    lowLinearRadius (Finset.Ico (3839) (4095)) (-1) = 1088246167863080946048335155879538506349 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (3839) (4095)) (1) = -683566979359665191802649798770312394249179727528 ∧
    lowLinearRadius (Finset.Ico (3839) (4095)) (1) = 1088795439380868088757035385353446515571 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (3839) (4095)) (2) = 683739528257664553205256721635626599945451357028 ∧
    lowLinearRadius (Finset.Ico (3839) (4095)) (2) = 1089070283190270148615429544251076504022 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache20224
