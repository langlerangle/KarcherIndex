module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate7424

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache7424
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-8961) (-8705)) n =
      blockLinearNumerator (-8961) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-8961) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 7424 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+7424 = -8961 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-8961) (-8705)) n =
      blockLinearRadius (-8961) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-8961) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 7424 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+7424 = -8961 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-8961) (-8705)) (-2) = -71418546362408270468403332158443950251413006659 ∧
    lowLinearRadius (Finset.Ico (-8961) (-8705)) (-2) = 318319179817479935152153841367166625228 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-8961) (-8705)) (-1) = 71410458719898693577169210089301150108464921132 ∧
    lowLinearRadius (Finset.Ico (-8961) (-8705)) (-1) = 318283131847729307660093299420222272068 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-8961) (-8705)) (1) = 71394288929227754500556195642644435347989343287 ∧
    lowLinearRadius (Finset.Ico (-8961) (-8705)) (1) = 318211060397851324744459259235279932738 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-8961) (-8705)) (2) = -71386206779822249111200073698140276293807231117 ∧
    lowLinearRadius (Finset.Ico (-8961) (-8705)) (2) = 318175036912178435553789311376139973084 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache7424
