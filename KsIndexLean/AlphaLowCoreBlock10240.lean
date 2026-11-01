module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate10240

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache10240
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-6145) (-5889)) n =
      blockLinearNumerator (-6145) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-6145) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 10240 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+10240 = -6145 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-6145) (-5889)) n =
      blockLinearRadius (-6145) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-6145) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 10240 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+10240 = -6145 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-6145) (-5889)) (-2) = -117433870478042727462128893275745086631221099167 ∧
    lowLinearRadius (Finset.Ico (-6145) (-5889)) (-2) = 573944269501230276187402615826908015840 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-6145) (-5889)) (-1) = 117414343479495255203731463996740812541819826898 ∧
    lowLinearRadius (Finset.Ico (-6145) (-5889)) (-1) = 573848830014309750924310493650029888468 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-6145) (-5889)) (1) = 117375308960651225165925798270952112196824212102 ∧
    lowLinearRadius (Finset.Ico (-6145) (-5889)) (1) = 573658046245259141277409665444551825915 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-6145) (-5889)) (2) = -117355801433878226244472646526452047063063422597 ∧
    lowLinearRadius (Finset.Ico (-6145) (-5889)) (2) = 573562701931472658544147999284179564127 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache10240
