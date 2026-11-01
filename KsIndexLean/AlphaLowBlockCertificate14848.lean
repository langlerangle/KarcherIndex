module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache14848

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache14848
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-1537 : ℤ)+i.val) : ℝ) *
        sample (2*((-1537 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-1537) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-1537) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 14848 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+14848 = -1537 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+14848 = -1537 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-1537) (-2) center = -724204346040147838613248700658407332147975035281 ∧ blockLinearRadius (-1537) (-2) radius = 5383302905197187307890835280221077006944 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-1537) (-1) center = 723686851852990003832200492356392096950560968057 ∧ blockLinearRadius (-1537) (-1) radius = 5379452568467454648813551702423983165799 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-1537) (1) center = 722654085136248042175670778879015432021400715862 ∧ blockLinearRadius (-1537) (1) radius = 5371768440268263939925044348138087065716 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-1537) (2) center = -722138809420964954779619515855425616602864729181 ∧ blockLinearRadius (-1537) (2) radius = 5367934625052221630435152751660582236671 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache14848
