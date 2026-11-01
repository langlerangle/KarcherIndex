module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate512

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache512
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-15873) (-15617)) n =
      blockLinearNumerator (-15873) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-15873) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 512 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+512 = -15873 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-15873) (-15617)) n =
      blockLinearRadius (-15873) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-15873) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 512 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+512 = -15873 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-15873) (-15617)) (-2) = -33464654584438769716614234185405663118462522151 ∧
    lowLinearRadius (Finset.Ico (-15873) (-15617)) (-2) = 131191501340947243481872208957798548177 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-15873) (-15617)) (-1) = 33462528926082740041338115749711825022871265350 ∧
    lowLinearRadius (Finset.Ico (-15873) (-15617)) (-1) = 131183168082502332985893597560789695738 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-15873) (-15617)) (1) = 33458278419410242060395319540027127498895363224 ∧
    lowLinearRadius (Finset.Ico (-15873) (-15617)) (1) = 131166504741240695307309152978617481189 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-15873) (-15617)) (2) = -33456153570990882201608143587484976166791217966 ∧
    lowLinearRadius (Finset.Ico (-15873) (-15617)) (2) = 131158174658020596660707807782528664231 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache512
