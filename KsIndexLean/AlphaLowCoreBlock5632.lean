module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate5632

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache5632
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-10753) (-10497)) n =
      blockLinearNumerator (-10753) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-10753) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 5632 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+5632 = -10753 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-10753) (-10497)) n =
      blockLinearRadius (-10753) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-10753) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 5632 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+5632 = -10753 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-10753) (-10497)) (-2) = -56116922728735790522234551632752493463191552793 ∧
    lowLinearRadius (Finset.Ico (-10753) (-10497)) (-2) = 239763520651769205878102892653282166362 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-10753) (-10497)) (-1) = 56111640048893665086588439455364383841098954908 ∧
    lowLinearRadius (Finset.Ico (-10753) (-10497)) (-1) = 239740949782345082681152718659992782751 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-10753) (-10497)) (1) = 56101077672566460204271599432376716401916615008 ∧
    lowLinearRadius (Finset.Ico (-10753) (-10497)) (1) = 239695820790378866298557335765149324217 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-10753) (-10497)) (2) = -56095797975519796346004532730980728957431808299 ∧
    lowLinearRadius (Finset.Ico (-10753) (-10497)) (2) = 239673262665437285491869233548811273031 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache5632
