module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate7936

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache7936
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-8449) (-8193)) n =
      blockLinearNumerator (-8449) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-8449) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 7936 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+7936 = -8449 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-8449) (-8193)) n =
      blockLinearRadius (-8449) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-8449) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 7936 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+7936 = -8449 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-8449) (-8193)) (-2) = -77189146684280546057712147058420684196947869593 ∧
    lowLinearRadius (Finset.Ico (-8449) (-8193)) (-2) = 348869884417603235272849275052026196701 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-8449) (-8193)) (-1) = 77179867458889458558944953204548003991960938567 ∧
    lowLinearRadius (Finset.Ico (-8449) (-8193)) (-1) = 348827944555029350598580476272317945562 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-8449) (-8193)) (1) = 77161315699989729026872034910589258318611019389 ∧
    lowLinearRadius (Finset.Ico (-8449) (-8193)) (1) = 348744095076137139538035613327729768751 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-8449) (-8193)) (2) = -77152043164872495875751088485367921869782951484 ∧
    lowLinearRadius (Finset.Ico (-8449) (-8193)) (2) = 348702185452548099974688835640669047045 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache7936
