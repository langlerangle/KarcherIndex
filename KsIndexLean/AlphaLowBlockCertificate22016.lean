module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache22016

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache22016
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((5631 : ℤ)+i.val) : ℝ) *
        sample (2*((5631 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (5631) n center : ℝ)/10^51| ≤
      (blockLinearRadius (5631) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 22016 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+22016 = 5631 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+22016 = 5631 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (5631) (-2) center = 393443486579484758765659306683054648554486841930 ∧ blockLinearRadius (5631) (-2) radius = 613530716441353358532809138167867555589 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (5631) (-1) center = -393511820621236176989304998237750531741010354996 ∧ blockLinearRadius (5631) (-1) radius = 613637276667937231537974295662379474284 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (5631) (1) center = -393648559951567470893013916860122630374095072978 ∧ blockLinearRadius (5631) (1) radius = 613850508224579141643237310656360539187 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (5631) (2) center = 393716965264916988320329401357333570890226701405 ∧ blockLinearRadius (5631) (2) radius = 613957179593263727224052066354826287865 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache22016
