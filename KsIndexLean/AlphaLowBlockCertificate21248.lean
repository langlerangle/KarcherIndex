module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache21248

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache21248
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((4863 : ℤ)+i.val) : ℝ) *
        sample (2*((4863 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (4863) n center : ℝ)/10^51| ≤
      (blockLinearRadius (4863) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 21248 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+21248 = 4863 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+21248 = 4863 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (4863) (-2) center = 486219148794388409079393695711716436247362020713 ∧ blockLinearRadius (4863) (-2) radius = 764412892560544322419007832399310853211 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (4863) (-1) center = -486316601413874367340089921383588375169224022277 ∧ blockLinearRadius (4863) (-1) radius = 764566105300149413190234822450538062115 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (4863) (1) center = -486511623919792713659786891420109037993310399395 ∧ blockLinearRadius (4863) (1) radius = 764872715146022123710477214524917263301 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (4863) (2) center = 486609193853281515096529470274295479275243200175 ∧ blockLinearRadius (4863) (2) radius = 765026112326272586040573934489503607042 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache21248
