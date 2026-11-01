module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache256

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache256
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-16129 : ℤ)+i.val) : ℝ) *
        sample (2*((-16129 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-16129) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-16129) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 256 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+256 = -16129 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+256 = -16129 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-16129) (-2) center = -32759603564144513110607490749681906467375188362 ∧ blockLinearRadius (-16129) (-2) radius = 127988985225523768038016464547759286556 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-16129) (-1) center = 32757555987566308930517804116380030080029713283 ∧ blockLinearRadius (-16129) (-1) radius = 127980985481816925537124984531785518295 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-16129) (1) center = 32753461602209525414130335471856306883177911673 ∧ blockLinearRadius (-16129) (1) radius = 127964988994158184361160970862208801310 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-16129) (2) center = -32751414793334980274461935684610646823636512803 ∧ blockLinearRadius (-16129) (2) radius = 127956992249831350372177683816477139834 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache256
