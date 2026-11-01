module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache28416

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache28416
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((12031 : ℤ)+i.val) : ℝ) *
        sample (2*((12031 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (12031) n center : ℝ)/10^51| ≤
      (blockLinearRadius (12031) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 28416 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+28416 = 12031 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+28416 = 12031 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (12031) (-2) center = 130455002849669614736438871700086604211657566015 ∧ blockLinearRadius (12031) (-2) radius = 194907957144239245758347976230234597360 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (12031) (-1) center = -130465732038150593496285993663475513365043260322 ∧ blockLinearRadius (12031) (-1) radius = 194923987258849317407474413260410356504 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (12031) (1) center = -130487195710670798309710567017699010334704298268 ∧ blockLinearRadius (12031) (1) radius = 194956055399999237002671149788829315054 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (12031) (2) center = 130497930195581363343871419800714160362656776503 ∧ blockLinearRadius (12031) (2) radius = 194972093427840928330867974227553258919 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache28416
