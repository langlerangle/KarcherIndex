module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache17920

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache17920
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((1535 : ℤ)+i.val) : ℝ) *
        sample (2*((1535 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (1535) n center : ℝ)/10^51| ≤
      (blockLinearRadius (1535) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 17920 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+17920 = 1535 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+17920 = 1535 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (1535) (-2) center = 2483198572520427951178795362718895793194712263336 ∧ blockLinearRadius (1535) (-2) radius = 4154305188337131193405054846885247927129 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (1535) (-1) center = -2484698230504993891032006291364278083411811137886 ∧ blockLinearRadius (1535) (-1) radius = 4156814341220122272354479983313585349144 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (1535) (1) center = -2487702997883143471977328549456660023646158208300 ∧ blockLinearRadius (1535) (1) radius = 4161841769016282942580589713035659334988 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (1535) (2) center = 2489208113899256620041014024385206982869525703481 ∧ blockLinearRadius (1535) (2) radius = 4164360055012373076334974291862396736170 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache17920
