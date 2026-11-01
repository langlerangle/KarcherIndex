module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache25600

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache25600
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((9215 : ℤ)+i.val) : ℝ) *
        sample (2*((9215 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (9215) n center : ℝ)/10^51| ≤
      (blockLinearRadius (9215) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 25600 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+25600 = 9215 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+25600 = 9215 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (9215) (-2) center = 192462940786638072537580083197959602226772299258 ∧ blockLinearRadius (9215) (-2) radius = 291933195852784997876839460548867093165 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (9215) (-1) center = -192483541467381202939996869880674016726546619084 ∧ blockLinearRadius (9215) (-1) radius = 291964443656169891135806813206818049318 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (9215) (1) center = -192524756062754870120618596475802978388783319732 ∧ blockLinearRadius (9215) (1) radius = 292026959336615879462503255799048285039 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (9215) (2) center = 192545369980219706298112808551886666628549888072 ∧ blockLinearRadius (9215) (2) radius = 292058227217976165741701592479330889954 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache25600
