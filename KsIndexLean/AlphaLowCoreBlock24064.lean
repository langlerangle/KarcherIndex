module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate24064

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache24064
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (7679) (7935)) n =
      blockLinearNumerator (7679) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (7679) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 24064 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+24064 = 7679 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (7679) (7935)) n =
      blockLinearRadius (7679) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (7679) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 24064 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+24064 = 7679 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (7679) (7935)) (-2) = 250935391258286964249019502012149183866381275024 ∧
    lowLinearRadius (Finset.Ico (7679) (7935)) (-2) = 384562089837352765493841972052320667629 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (7679) (7935)) (-1) = -250967536633916724779221632582126786545082973291 ∧
    lowLinearRadius (Finset.Ico (7679) (7935)) (-1) = 384611353339552930877632097489235888859 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (7679) (7935)) (1) = -251031852101083204405337360202737008363776844594 ∧
    lowLinearRadius (Finset.Ico (7679) (7935)) (1) = 384709918221823875683909419809430385506 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (7679) (7935)) (2) = 251064022198955817874377938969521875108768342295 ∧
    lowLinearRadius (Finset.Ico (7679) (7935)) (2) = 384759219611604653523685692338926687586 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache24064
