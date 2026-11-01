module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate4864

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache4864
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-11521) (-11265)) n =
      blockLinearNumerator (-11521) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-11521) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 4864 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+4864 = -11521 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-11521) (-11265)) n =
      blockLinearRadius (-11521) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-11521) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 4864 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+4864 = -11521 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-11521) (-11265)) (-2) = -51215907577838617621170315061571822582309643685 ∧
    lowLinearRadius (Finset.Ico (-11521) (-11265)) (-2) = 215425159998684055219711676535755166429 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-11521) (-11265)) (-1) = 51211411362295120819248054614816060883225230952 ∧
    lowLinearRadius (Finset.Ico (-11521) (-11265)) (-1) = 215406247768316350369459599683961470359 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-11521) (-11265)) (1) = 51202421299213298066786894191323177522323830339 ∧
    lowLinearRadius (Finset.Ico (-11521) (-11265)) (1) = 215368433268108642799901988586130214487 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-11521) (-11265)) (2) = -51197927451259274952977525121793901754177203046 ∧
    lowLinearRadius (Finset.Ico (-11521) (-11265)) (2) = 215349530996520078886240310308916090749 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache4864
