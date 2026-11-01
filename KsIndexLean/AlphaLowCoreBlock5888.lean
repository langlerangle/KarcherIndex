module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate5888

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache5888
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-10497) (-10241)) n =
      blockLinearNumerator (-10497) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-10497) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 5888 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+5888 = -10497 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-10497) (-10241)) n =
      blockLinearRadius (-10497) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-10497) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 5888 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+5888 = -10497 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-10497) (-10241)) (-2) = -57935941217339331434403853546306911741844171314 ∧
    lowLinearRadius (Finset.Ico (-10497) (-10241)) (-2) = 248903314655282442673665449488406387247 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-10497) (-10241)) (-1) = 57930352604923221083047124488072248799315487019 ∧
    lowLinearRadius (Finset.Ico (-10497) (-10241)) (-1) = 248879304686316138964181740124090550033 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-10497) (-10241)) (1) = 57919178614161217899534293640244100216803400764 ∧
    lowLinearRadius (Finset.Ico (-10497) (-10241)) (1) = 248831298642855443022937114563769436185 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-10497) (-10241)) (2) = -57913593235191512946548820252972637584128412055 ∧
    lowLinearRadius (Finset.Ico (-10497) (-10241)) (2) = 248807302565680948310995932937910171359 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache5888
