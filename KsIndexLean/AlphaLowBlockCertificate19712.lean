module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache19712

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache19712
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((3327 : ℤ)+i.val) : ℝ) *
        sample (2*((3327 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (3327) n center : ℝ)/10^51| ≤
      (blockLinearRadius (3327) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 19712 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+19712 = 3327 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+19712 = 3327 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (3327) (-2) center = 838217580536657837747713643147066457189252478401 ∧ blockLinearRadius (3327) (-2) radius = 1345629902215747535649361483791099790281 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (3327) (-1) center = -838460395799697312434842672828764572257082303594 ∧ blockLinearRadius (3327) (-1) radius = 1346019715008922373949601242430182084985 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (3327) (1) center = -838946448796867619351528941590683002177946808288 ∧ blockLinearRadius (3327) (1) radius = 1346800018842989705090270214820183594277 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (3327) (2) center = 839189686776199019213174995257397118837078233377 ∧ blockLinearRadius (3327) (2) radius = 1347190510277544694284532474754120938692 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache19712
