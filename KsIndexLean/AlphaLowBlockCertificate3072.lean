module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache3072

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache3072
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-13313 : ℤ)+i.val) : ℝ) *
        sample (2*((-13313 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-13313) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-13313) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 3072 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+3072 = -13313 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+3072 = -13313 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-13313) (-2) center = -42278428551831569922242879876074051416072696604 ∧ blockLinearRadius (-13313) (-2) radius = 172194462255428423673890933107535730956 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-13313) (-1) center = 42275221520301752695609928558935007008537892932 ∧ blockLinearRadius (-13313) (-1) radius = 172181400349591082196446980263028819862 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-13313) (1) center = 42268808916683421014552039409571334788883686042 ∧ blockLinearRadius (-13313) (1) radius = 172155282482109730879945116445028270696 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-13313) (2) center = -42265603344373531097666618414656362237228410743 ∧ blockLinearRadius (-13313) (2) radius = 172142226519564069459375049115464226429 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache3072
