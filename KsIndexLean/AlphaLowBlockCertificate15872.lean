module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache15872

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache15872
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-513 : ℤ)+i.val) : ℝ) *
        sample (2*((-513 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-513) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-513) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 15872 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+15872 = -513 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+15872 = -513 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-513) (-2) center = -3245749297524216780583917315811828402285368387056 ∧ blockLinearRadius (-513) (-2) radius = 42898076232696682373034473904033519874051 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-513) (-1) center = 3236599374496522641937348276782465893325408937700 ∧ blockLinearRadius (-513) (-1) radius = 42774579155540491435912637688944144319432 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-513) (1) center = 3218459442409174247946492707699489744460831176444 ∧ blockLinearRadius (-513) (1) radius = 42529786564854625039102369753435696331768 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-513) (2) center = -3209468470772943507814096847546915856049187505654 ∧ blockLinearRadius (-513) (2) radius = 42408477558540938933394266873540537649181 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache15872
