module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate6912

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache6912
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-9473) (-9217)) n =
      blockLinearNumerator (-9473) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-9473) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 6912 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+6912 = -9473 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-9473) (-9217)) n =
      blockLinearRadius (-9473) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-9473) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 6912 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+6912 = -9473 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-9473) (-9217)) (-2) = -66361977769251643160460643707781423375757415967 ∧
    lowLinearRadius (Finset.Ico (-9473) (-9217)) (-2) = 291951905320902027525342459567168026097 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-9473) (-9217)) (-1) = 66354874650394851996903376116348466938123231448 ∧
    lowLinearRadius (Finset.Ico (-9473) (-9217)) (-1) = 291920655514778345088555665920865875661 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-9473) (-9217)) (1) = 66340672973725542736779418499979218562035486081 ∧
    lowLinearRadius (Finset.Ico (-9473) (-9217)) (1) = 291858175968899494925627306160079076449 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-9473) (-9217)) (2) = -66333574414936824402612346532754912917971582948 ∧
    lowLinearRadius (Finset.Ico (-9473) (-9217)) (2) = 291826946224849460852553145167055476438 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache6912
