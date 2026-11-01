module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache512

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache512
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-15873 : ℤ)+i.val) : ℝ) *
        sample (2*((-15873 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-15873) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-15873) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 512 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+512 = -15873 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+512 = -15873 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-15873) (-2) center = -33464654584438769716614234185405663118462522151 ∧ blockLinearRadius (-15873) (-2) radius = 131191501340947243481872208957798548177 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-15873) (-1) center = 33462528926082740041338115749711825022871265350 ∧ blockLinearRadius (-15873) (-1) radius = 131183168082502332985893597560789695738 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-15873) (1) center = 33458278419410242060395319540027127498895363224 ∧ blockLinearRadius (-15873) (1) radius = 131166504741240695307309152978617481189 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-15873) (2) center = -33456153570990882201608143587484976166791217966 ∧ blockLinearRadius (-15873) (2) radius = 131158174658020596660707807782528664231 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache512
