module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate25600

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache25600
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (9215) (9471)) n =
      blockLinearNumerator (9215) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (9215) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 25600 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+25600 = 9215 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (9215) (9471)) n =
      blockLinearRadius (9215) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (9215) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 25600 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+25600 = 9215 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (9215) (9471)) (-2) = 192462940786638072537580083197959602226772299258 ∧
    lowLinearRadius (Finset.Ico (9215) (9471)) (-2) = 291933195852784997876839460548867093165 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (9215) (9471)) (-1) = -192483541467381202939996869880674016726546619084 ∧
    lowLinearRadius (Finset.Ico (9215) (9471)) (-1) = 291964443656169891135806813206818049318 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (9215) (9471)) (1) = -192524756062754870120618596475802978388783319732 ∧
    lowLinearRadius (Finset.Ico (9215) (9471)) (1) = 292026959336615879462503255799048285039 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (9215) (9471)) (2) = 192545369980219706298112808551886666628549888072 ∧
    lowLinearRadius (Finset.Ico (9215) (9471)) (2) = 292058227217976165741701592479330889954 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache25600
