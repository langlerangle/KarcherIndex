module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate8448

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache8448
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-7937) (-7681)) n =
      blockLinearNumerator (-7937) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-7937) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 8448 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+8448 = -7937 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-7937) (-7681)) n =
      blockLinearRadius (-7937) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-7937) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 8448 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+8448 = -7937 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-7937) (-7681)) (-2) = -83827382073450262767019513273312084954889953837 ∧
    lowLinearRadius (Finset.Ico (-7937) (-7681)) (-2) = 384591526107935828020952868757836685474 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-7937) (-7681)) (-1) = 83816643774352795459137679356386605770911618578 ∧
    lowLinearRadius (Finset.Ico (-7937) (-7681)) (-1) = 384542258834531299677611316180924015933 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-7937) (-7681)) (1) = 83795175428248222926059061144491255044402335286 ∧
    lowLinearRadius (Finset.Ico (-7937) (-7681)) (1) = 384443762149083685063920100500869955438 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-7937) (-7681)) (2) = -83784445379127363672201463424348848839685816677 ∧
    lowLinearRadius (Finset.Ico (-7937) (-7681)) (2) = 384394532727342292040185912067803758150 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache8448
