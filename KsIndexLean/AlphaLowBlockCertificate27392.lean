module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache27392

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache27392
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((11007 : ℤ)+i.val) : ℝ) *
        sample (2*((11007 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (11007) n center : ℝ)/10^51| ≤
      (blockLinearRadius (11007) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 27392 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+27392 = 11007 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+27392 = 11007 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (11007) (-2) center = 148540984488823808857704896252836050541916679432 ∧ blockLinearRadius (11007) (-2) radius = 223054007193000363172749073584056892576 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (11007) (-1) center = -148554324753087008696548322489210811545580671383 ∧ blockLinearRadius (11007) (-1) radius = 223074039421385552665332293242476578535 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (11007) (1) center = -148581012471647753412801111809461948555439340641 ∧ blockLinearRadius (11007) (1) radius = 223114114675001596166144139649067426052 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (11007) (2) center = 148594359927237214628835583711135959327661406155 ∧ blockLinearRadius (11007) (2) radius = 223134157702172448778909783202333861259 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache27392
