module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache24576

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache24576
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((8191 : ℤ)+i.val) : ℝ) *
        sample (2*((8191 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (8191) n center : ℝ)/10^51| ≤
      (blockLinearRadius (8191) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 24576 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+24576 = 8191 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+24576 = 8191 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (8191) (-2) center = 228458350868937867771245615720014144007101697428 ∧ blockLinearRadius (8191) (-2) radius = 348844808028213566209328105690312912298 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (8191) (-1) center = -228485815172757640810205733358551226077846475425 ∧ blockLinearRadius (8191) (-1) radius = 348886744875960415148162829948623239619 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (8191) (1) center = -228540763596585217340365208653169232685986764617 ∧ blockLinearRadius (8191) (1) radius = 348970648830084389140687275361589400770 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (8191) (2) center = 228568247721359930164112667812483683468597933331 ∧ blockLinearRadius (8191) (2) radius = 349012615943740451922201506637169331603 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache24576
