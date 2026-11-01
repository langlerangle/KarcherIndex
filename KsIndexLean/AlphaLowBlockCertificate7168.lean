module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache7168

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache7168
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-9217 : ℤ)+i.val) : ℝ) *
        sample (2*((-9217 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-9217) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-9217) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 7168 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+7168 = -9217 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+7168 = -9217 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-9217) (-2) center = -68809179679232743992551994937140672088790235501 ∧ blockLinearRadius (-9217) (-2) radius = 304664529947852916001018247157707346971 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-9217) (-1) center = 68801607093446102754486625763731682690261560029 ∧ blockLinearRadius (-9217) (-1) radius = 304631000503509361399774357740057186421 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-9217) (1) center = 68786466921370839081842474559185207663541947705 ∧ blockLinearRadius (-9217) (1) radius = 304563963751640137538547695101953503420 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-9217) (2) center = -68778899333982025223529095752735146839876112030 ∧ blockLinearRadius (-9217) (2) radius = 304530456439242957338890353397443709895 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache7168
