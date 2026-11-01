module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate11008

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache11008
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-5377) (-5121)) n =
      blockLinearNumerator (-5377) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-5377) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 11008 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+11008 = -5377 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-5377) (-5121)) n =
      blockLinearRadius (-5377) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-5377) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 11008 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+11008 = -5377 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-5377) (-5121)) (-2) = -139966918986264221555834986313655207609858305884 ∧
    lowLinearRadius (Finset.Ico (-5377) (-5121)) (-2) = 707946319732024990986181197509332942775 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-5377) (-5121)) (-1) = 139940236386297086699146062242873570225622676756 ∧
    lowLinearRadius (Finset.Ico (-5377) (-5121)) (-1) = 707811353550633948151221967521461386804 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-5377) (-5121)) (1) = 139886901700609487905628747771575758491222870475 ∧
    lowLinearRadius (Finset.Ico (-5377) (-5121)) (1) = 707541575543079430193612331019648305803 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-5377) (-5121)) (2) = -139860249603256896998690501081903000358640346628 ∧
    lowLinearRadius (Finset.Ico (-5377) (-5121)) (2) = 707406763658072294483692589792753837328 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache11008
