module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate21760

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache21760
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (5375) (5631)) n =
      blockLinearNumerator (5375) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (5375) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 21760 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+21760 = 5375 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (5375) (5631)) n =
      blockLinearRadius (5375) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (5375) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 21760 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+21760 = 5375 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (5375) (5631)) (-2) = 420812944171936615177171035475466670651002258611 ∧
    lowLinearRadius (Finset.Ico (5375) (5631)) (-2) = 657913772669104398029178227588987077093 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (5375) (5631)) (-1) = -420889434194032081678297652749602818047688706275 ∧
    lowLinearRadius (Finset.Ico (5375) (5631)) (-1) = 658033361091161576572218705901522334233 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (5375) (5631)) (1) = -421042497703915388178552297991609019192026798271 ∧
    lowLinearRadius (Finset.Ico (5375) (5631)) (1) = 658272668431159126514459246522101561924 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (5375) (5631)) (2) = 421119071222073403766852661531503273461954566014 ∧
    lowLinearRadius (Finset.Ico (5375) (5631)) (2) = 658392387396582762872526035768636023308 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache21760
