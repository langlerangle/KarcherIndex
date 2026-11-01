module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate4608

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache4608
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-11777) (-11521)) n =
      blockLinearNumerator (-11777) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-11777) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 4608 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+4608 = -11777 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-11777) (-11521)) n =
      blockLinearRadius (-11777) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-11777) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 4608 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+4608 = -11777 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-11777) (-11521)) (-2) = -49745511863550253452011751314439715672445744094 ∧
    lowLinearRadius (Finset.Ico (-11777) (-11521)) (-2) = 208207636319452639082979130456199340389 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-11777) (-11521)) (-1) = 49741240732036052911363401198370183045962060247 ∧
    lowLinearRadius (Finset.Ico (-11777) (-11521)) (-1) = 208189759527785875492423816441250196520 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-11777) (-11521)) (1) = 49732700669025176752710073064953946253417080868 ∧
    lowLinearRadius (Finset.Ico (-11777) (-11521)) (1) = 208154015152692964793595267150134146547 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-11777) (-11521)) (2) = -49728431737150782621699717244680026002379171986 ∧
    lowLinearRadius (Finset.Ico (-11777) (-11521)) (2) = 208136147567685851164317523485694571358 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache4608
