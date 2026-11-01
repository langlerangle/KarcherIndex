module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache8960

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache8960
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-7425 : ℤ)+i.val) : ℝ) *
        sample (2*((-7425 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-7425) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-7425) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 8960 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+8960 = -7425 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+8960 = -7425 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-7425) (-2) center = -91532873353856276220993231328302809032203854402 ∧ blockLinearRadius (-7425) (-2) radius = 426792022664277863582581825255530312983 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-7425) (-1) center = 91520324774946329923280003584787027451644898653 ∧ blockLinearRadius (-7425) (-1) radius = 426733510733478997322979502426692846706 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-7425) (1) center = 91495237937340857277724198640632948314363575382 ∧ blockLinearRadius (-7425) (1) radius = 426616534994503578950940355534140151653 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-7425) (2) center = -91482699675816241804709806460859668825471142091 ∧ blockLinearRadius (-7425) (2) radius = 426558071173134807291612860870080083485 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache8960
