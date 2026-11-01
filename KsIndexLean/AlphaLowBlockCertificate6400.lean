module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache6400

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache6400
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-9985 : ℤ)+i.val) : ℝ) *
        sample (2*((-9985 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-9985) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-9985) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 6400 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+6400 = -9985 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+6400 = -9985 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-9985) (-2) center = -61899446069750112358039497954410108356932219041 ∧ blockLinearRadius (-9985) (-2) radius = 269010079886278441978158017955785301434 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-9985) (-1) center = 61893164873428686562988254031629798754449734176 ∧ blockLinearRadius (-9985) (-1) radius = 268982781955388400197467975270128220253 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-9985) (1) center = 61880606304500705375741712759260414987086675002 ∧ blockLinearRadius (-9985) (1) radius = 268928202711595972687576045253458671590 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-9985) (2) center = -61874328931118282205240758336028267367438115321 ∧ blockLinearRadius (-9985) (2) radius = 268900921395321597436972083535325077795 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache6400
