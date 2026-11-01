module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache6656

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache6656
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-9729 : ℤ)+i.val) : ℝ) *
        sample (2*((-9729 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-9729) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-9729) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 6656 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+6656 = -9729 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+6656 = -9729 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-9729) (-2) center = -64062899459903854243240043038392184088366916884 ∧ blockLinearRadius (-9729) (-2) radius = 280093059964151491423532986224105859024 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-9729) (-1) center = 64056225329652567326067353478909458976529416021 ∧ blockLinearRadius (-9729) (-1) radius = 280063879222011525851461611493088881168 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-9729) (1) center = 64042881240429203626834634948789141742505233547 ∧ blockLinearRadius (-9729) (1) radius = 280005535975714799485620497974945656988 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-9729) (2) center = -64036211280588160271876929756698008143114901577 ∧ blockLinearRadius (-9729) (2) radius = 279976373467758625598221681811365387921 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache6656
