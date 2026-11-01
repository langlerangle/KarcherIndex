module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate2816

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache2816
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-13569) (-13313)) n =
      blockLinearNumerator (-13569) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-13569) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 2816 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+2816 = -13569 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-13569) (-13313)) n =
      blockLinearRadius (-13569) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-13569) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 2816 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+2816 = -13569 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-13569) (-13313)) (-2) = -41222518177183067309337181320043466060158588101 ∧
    lowLinearRadius (Finset.Ico (-13569) (-13313)) (-2) = 167192347268802470571542521779253948778 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-13569) (-13313)) (-1) = 41219450810808206715108746046094190775137598978 ∧
    lowLinearRadius (Finset.Ico (-13569) (-13313)) (-1) = 167179906409352177546189435399732406947 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-13569) (-13313)) (1) = 41213317447351955411462329123434801176774487261 ∧
    lowLinearRadius (Finset.Ico (-13569) (-13313)) (1) = 167155030244173405607171763012590646208 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-13569) (-13313)) (2) = -41210251450066819692496185333471752999157769744 ∧
    lowLinearRadius (Finset.Ico (-13569) (-13313)) (2) = 167142594937618551220741393191991212125 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache2816
