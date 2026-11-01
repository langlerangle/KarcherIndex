module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache21760

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache21760
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((5375 : ℤ)+i.val) : ℝ) *
        sample (2*((5375 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (5375) n center : ℝ)/10^51| ≤
      (blockLinearRadius (5375) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 21760 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+21760 = 5375 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+21760 = 5375 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (5375) (-2) center = 420812944171936615177171035475466670651002258611 ∧ blockLinearRadius (5375) (-2) radius = 657913772669104398029178227588987077093 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (5375) (-1) center = -420889434194032081678297652749602818047688706275 ∧ blockLinearRadius (5375) (-1) radius = 658033361091161576572218705901522334233 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (5375) (1) center = -421042497703915388178552297991609019192026798271 ∧ blockLinearRadius (5375) (1) radius = 658272668431159126514459246522101561924 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (5375) (2) center = 421119071222073403766852661531503273461954566014 ∧ blockLinearRadius (5375) (2) radius = 658392387396582762872526035768636023308 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache21760
