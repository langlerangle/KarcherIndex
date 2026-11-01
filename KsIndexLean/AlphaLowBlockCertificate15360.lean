module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache15360

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache15360
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-1025 : ℤ)+i.val) : ℝ) *
        sample (2*((-1025 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-1025) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-1025) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 15360 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+15360 = -1025 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+15360 = -1025 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-1025) (-2) center = -1241642143522550698672608919891157235013289939468 ∧ blockLinearRadius (-1025) (-2) radius = 10890001921045591416424741124935478686643 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-1025) (-1) center = 1240235657079420639713718000343517373923304344332 ∧ blockLinearRadius (-1025) (-1) radius = 10877633573426418851810138405289439335797 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-1025) (1) center = 1237432287158678595440817432520211975815360600925 ∧ blockLinearRadius (-1025) (1) radius = 10852981544739622826242029244601579805898 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-1025) (2) center = -1236035381703695150552066042478323021850561868241 ∧ blockLinearRadius (-1025) (2) radius = 10840697669408635629411840806849354792890 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache15360
