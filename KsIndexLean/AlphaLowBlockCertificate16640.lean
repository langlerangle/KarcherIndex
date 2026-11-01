module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache16640

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache16640
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((255 : ℤ)+i.val) : ℝ) *
        sample (2*((255 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (255) n center : ℝ)/10^51| ≤
      (blockLinearRadius (255) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 16640 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+16640 = 255 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+16640 = 255 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (255) (-2) center = 23518923398818573690240900852955274358809367503256 ∧ blockLinearRadius (255) (-2) radius = 42826684829587308160732517681518098192006 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (255) (-1) center = -23586483563820932107664818146872509011456128094769 ∧ blockLinearRadius (255) (-1) radius = 42949968559751262173297895289031220419386 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (255) (1) center = -23722820790508231951071914487009784964288423855434 ∧ blockLinearRadius (255) (1) radius = 43198761017279810946918158827666758711251 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (255) (2) center = 23791605443288113861350702339862559170521639502920 ∧ blockLinearRadius (255) (2) radius = 43324283649061986214962188420748407302190 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache16640
