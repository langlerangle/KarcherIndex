module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate5376

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache5376
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-11009) (-10753)) n =
      blockLinearNumerator (-11009) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-11009) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 5376 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+5376 = -11009 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-11009) (-10753)) n =
      blockLinearRadius (-11009) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-11009) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 5376 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+5376 = -11009 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-11009) (-10753)) (-2) = -54395323183648026236707469979782722699495323900 ∧
    lowLinearRadius (Finset.Ico (-11009) (-10753)) (-2) = 231165691764149943887112895531288257376 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-11009) (-10753)) (-1) = 54390323080877927910072363183774175125767700437 ∧
    lowLinearRadius (Finset.Ico (-11009) (-10753)) (-1) = 231144442433760834114244200910598332007 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-11009) (-10753)) (1) = 54380325632661379167528255685408963184008662274 ∧
    lowLinearRadius (Finset.Ico (-11009) (-10753)) (1) = 231101955491119402506471244730750607974 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-11009) (-10753)) (2) = -54375328286708106801080577125172649032817054426 ∧
    lowLinearRadius (Finset.Ico (-11009) (-10753)) (2) = 231080717876713154901960838756405665780 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache5376
