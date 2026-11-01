module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache32768

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache32768
def center (i : Fin 2) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 2) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 2, (rationalKernelWeight n ((16383 : ℤ)+i.val) : ℝ) *
        sample (2*((16383 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (16383) n center : ℝ)/10^51| ≤
      (blockLinearRadius (16383) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 32768 2 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+32768 = 16383 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+32768 = 16383 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (16383) (-2) center = 656434477014201293226544946598163434620030393 ∧ blockLinearRadius (16383) (-2) radius = 964068236925990776247843794542252686 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (16383) (-1) center = -656474540149906313142397899521581927414023201 ∧ blockLinearRadius (16383) (-1) radius = 964127075390391086621955813921501127 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (16383) (1) center = -656554681093770421701639444327619495429298798 ∧ blockLinearRadius (16383) (1) radius = 964244773867796209791645911591985521 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (16383) (2) center = 656594758903720800069100465620039605902187522 ∧ blockLinearRadius (16383) (2) radius = 964303633883431788622309373334265772 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache32768
