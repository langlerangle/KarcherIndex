module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache25344

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache25344
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((8959 : ℤ)+i.val) : ℝ) *
        sample (2*((8959 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (8959) n center : ℝ)/10^51| ≤
      (blockLinearRadius (8959) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 25344 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+25344 = 8959 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+25344 = 8959 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (8959) (-2) center = 200523480181880528993774129434668656833692774610 ∧ blockLinearRadius (8959) (-2) radius = 304644462032204942277812978484426627146 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (8959) (-1) center = -200545548439579228678781638236407048534435680159 ∧ blockLinearRadius (8959) (-1) radius = 304677989267856704184628072925630844342 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (8959) (1) center = -200589699531247921672278839810982451268923296579 ∧ blockLinearRadius (8959) (1) radius = 304745065884267538176442239506882048388 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (8959) (2) center = 200611782368427730914682349227946190084123406104 ∧ blockLinearRadius (8959) (2) radius = 304778615269903165195399983243415950830 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache25344
