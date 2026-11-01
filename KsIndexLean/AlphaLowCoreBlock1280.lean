module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate1280

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache1280
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-15105) (-14849)) n =
      blockLinearNumerator (-15105) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-15105) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 1280 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+1280 = -15105 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-15105) (-14849)) n =
      blockLinearRadius (-15105) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-15105) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 1280 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+1280 = -15105 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-15105) (-14849)) (-2) = -35747000864098797004017874337281276580480987645 ∧
    lowLinearRadius (Finset.Ico (-15105) (-14849)) (-2) = 141640426634825729470117803339387580068 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-15105) (-14849)) (-1) = 35744613776818825282480350765702985645568395600 ∧
    lowLinearRadius (Finset.Ico (-15105) (-14849)) (-1) = 141630968223954481954027710849892351642 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-15105) (-14849)) (1) = 35739840558573536674123660271685301269468539988 ∧
    lowLinearRadius (Finset.Ico (-15105) (-14849)) (1) = 141612055191459285100973808033435999267 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-15105) (-14849)) (2) = -35737454427480518980084861848141998058389078691 ∧
    lowLinearRadius (Finset.Ico (-15105) (-14849)) (2) = 141602600569329338647305524837137957629 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache1280
