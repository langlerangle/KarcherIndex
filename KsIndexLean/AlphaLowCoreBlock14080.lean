module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate14080

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache14080
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-2305) (-2049)) n =
      blockLinearNumerator (-2305) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-2305) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 14080 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+14080 = -2305 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-2305) (-2049)) n =
      blockLinearRadius (-2305) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-2305) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 14080 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+14080 = -2305 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-2305) (-2049)) (-2) = -424994739446261224033899792554051668413948291140 ∧
    lowLinearRadius (Finset.Ico (-2305) (-2049)) (-2) = 2745484295201305394003392695957214615860 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-2305) (-2049)) (-1) = 424798924285370516956815715992888481149331239540 ∧
    lowLinearRadius (Finset.Ico (-2305) (-2049)) (-1) = 2744218876787544228539477930445251835905 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-2305) (-2049)) (1) = 424407835416693988666979496051484036056273043801 ∧
    lowLinearRadius (Finset.Ico (-2305) (-2049)) (1) = 2741691540223159582401195920541508740771 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-2305) (-2049)) (2) = -424212561209503141530384520986388996342945898012 ∧
    lowLinearRadius (Finset.Ico (-2305) (-2049)) (2) = 2740429618842969762408988591479653243095 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache14080
