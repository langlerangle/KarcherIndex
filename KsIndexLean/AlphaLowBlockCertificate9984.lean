module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache9984

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache9984
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-6401 : ℤ)+i.val) : ℝ) *
        sample (2*((-6401 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-6401) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-6401) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 9984 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+9984 = -6401 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+9984 = -6401 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-6401) (-2) center = -111293098537576124310194503099877059812301714875 ∧ blockLinearRadius (-6401) (-2) radius = 538357661210493453058891354743422774371 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-6401) (-1) center = 111275348460700365713972698208856157473247441377 ∧ blockLinearRadius (-6401) (-1) radius = 538271795899806458326937753056205370762 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-6401) (1) center = 111239865289590514192751813097452191268869659860 ∧ blockLinearRadius (-6401) (1) radius = 538100147434111364247510034705480961099 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-6401) (2) center = -111222132189940404800447290732957980715067796502 ∧ blockLinearRadius (-6401) (2) radius = 538014364252901705094409612510672847675 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache9984
