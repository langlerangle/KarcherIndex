module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate16896

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache16896
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (511) (767)) n =
      blockLinearNumerator (511) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (511) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 16896 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+16896 = 511 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (511) (767)) n =
      blockLinearRadius (511) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (511) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 16896 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+16896 = 511 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (511) (767)) (-2) = 10488934404897950690333293655564247105918346703270 ∧
    lowLinearRadius (Finset.Ico (511) (767)) (-2) = 18523389837006216790266266628512630444110 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (511) (767)) (-1) = -10505888302140084147619732324540882535669822202589 ∧
    lowLinearRadius (Finset.Ico (511) (767)) (-1) = 18553352567424494937128599851217374686698 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (511) (767)) (1) = -10539963297612345693502215548873990905811298004979 ∧
    lowLinearRadius (Finset.Ico (511) (767)) (1) = 18613573738643811443870673799708273276805 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (511) (767)) (2) = 10557084953681458428635417723724301358397061745012 ∧
    lowLinearRadius (Finset.Ico (511) (767)) (2) = 18643833166725263558292655891836913271463 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache16896
