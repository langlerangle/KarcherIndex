module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache5120

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache5120
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-11265 : ℤ)+i.val) : ℝ) *
        sample (2*((-11265 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-11265) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-11265) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 5120 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+5120 = -11265 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+5120 = -11265 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-11265) (-2) center = -52763850565117218599879467272074782077122526040 ∧ blockLinearRadius (-11265) (-2) radius = 223066025528461349298319469715696938090 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-11265) (-1) center = 52759111950001655290652503736002646138021524394 ∧ blockLinearRadius (-11265) (-1) radius = 223045992220676042073959056328428772288 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-11265) (1) center = 52749637272817234574804307814797807888215014960 ∧ blockLinearRadius (-11265) (1) radius = 223005936398654421828547133476142688608 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-11265) (2) center = -52744901210289892362118252923211328141435243227 ∧ blockLinearRadius (-11265) (2) radius = 222985913882479747493129351693412908186 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache5120
