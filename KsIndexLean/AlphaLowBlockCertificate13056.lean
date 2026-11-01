module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache13056

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache13056
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-3329 : ℤ)+i.val) : ℝ) *
        sample (2*((-3329 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-3329) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-3329) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 13056 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+13056 = -3329 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+13056 = -3329 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-3329) (-2) center = -262522405825711532856281832200183153668904066513 ∧ blockLinearRadius (-3329) (-2) radius = 1515140022463813927834166916312567990578 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-3329) (-1) center = 262440268633688204073780837930371863905508555122 ∧ blockLinearRadius (-3329) (-1) radius = 1514665899433760133786837503615725688689 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-3329) (1) center = 262276148428330100169007830328366572664856428736 ∧ blockLinearRadius (-3329) (1) radius = 1513718543476634251216984331723500037565 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-3329) (2) center = -262194165318505219468868357472659952487020992184 ∧ blockLinearRadius (-3329) (2) radius = 1513245309992423518652664869180602549776 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache13056
