module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache17408

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache17408
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((1023 : ℤ)+i.val) : ℝ) *
        sample (2*((1023 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (1023) n center : ℝ)/10^51| ≤
      (blockLinearRadius (1023) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 17408 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+17408 = 1023 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+17408 = 1023 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (1023) (-2) center = 4303091364569578186094040179441107525878530142327 ∧ blockLinearRadius (1023) (-2) radius = 7349464591711430973750142312297382838903 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (1023) (-1) center = -4306865337023390425271118302783418141114838047103 ∧ blockLinearRadius (1023) (-1) radius = 7355911825964217756742402736026942515177 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (1023) (1) center = -4314433258843138006644620278692229049079996699032 ∧ blockLinearRadius (1023) (1) radius = 7368840429642022326494211211462635434680 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (1023) (2) center = 4318227243633545341771286870827415694765548923364 ∧ blockLinearRadius (1023) (2) radius = 7375321859611582549759564984335260322177 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache17408
