module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache29952

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache29952
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((13567 : ℤ)+i.val) : ℝ) *
        sample (2*((13567 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (13567) n center : ℝ)/10^51| ≤
      (blockLinearRadius (13567) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 29952 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+29952 = 13567 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+29952 = 13567 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (13567) (-2) center = 109455663054761199808577425388398526075076072571 ∧ blockLinearRadius (13567) (-2) radius = 162418951504545940647591191088783386136 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (13567) (-1) center = -109463655428531516251428805117887300817318488389 ∧ blockLinearRadius (13567) (-1) radius = 162430811239395864118190337701533088022 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (13567) (1) center = -109479643678269880264992502016025769615874825397 ∧ blockLinearRadius (13567) (1) radius = 162454535905950517759335011974922738695 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (13567) (2) center = 109487639554749525616235462175318790028005206880 ∧ blockLinearRadius (13567) (2) radius = 162466400838414400907988215216918491133 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache29952
