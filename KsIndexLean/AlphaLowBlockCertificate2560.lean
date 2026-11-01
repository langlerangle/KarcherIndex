module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache2560

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache2560
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-13825 : ℤ)+i.val) : ℝ) *
        sample (2*((-13825 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-13825) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-13825) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 2560 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+2560 = -13825 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+2560 = -13825 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-13825) (-2) center = -40211741887345958973528590237981098812934493187 ∧ blockLinearRadius (-13825) (-2) radius = 162426083828218607694123369964247915402 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-13825) (-1) center = 40208805668492882450577846057884207827563765707 ∧ blockLinearRadius (-13825) (-1) radius = 162414223572555682321729445199337049381 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-13825) (1) center = 40202934517033898291596656664481830260355696404 ∧ blockLinearRadius (-13825) (1) radius = 162390508256795043229930363523507945316 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-13825) (2) center = -40199999584240180048116632653420294719092604667 ∧ blockLinearRadius (-13825) (2) radius = 162378653195938697392121976509535729334 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache2560
