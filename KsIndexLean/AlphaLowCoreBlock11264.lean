module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate11264

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache11264
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-5121) (-4865)) n =
      blockLinearNumerator (-5121) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-5121) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 11264 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+11264 = -5121 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-5121) (-4865)) n =
      blockLinearRadius (-5121) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-5121) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 11264 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+11264 = -5121 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-5121) (-4865)) (-2) = -149229855235432233398475394617530972753716428252 ∧
    lowLinearRadius (Finset.Ico (-5121) (-4865)) (-2) = 764503986831460239216113498159582396941 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-5121) (-4865)) (-1) = 149199946490567562216547704928186042812145468189 ∧
    lowLinearRadius (Finset.Ico (-5121) (-4865)) (-1) = 764350755829697699380959477900026479316 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-5121) (-4865)) (1) = 149140164960283115027047312649541433528382921505 ∧
    lowLinearRadius (Finset.Ico (-5121) (-4865)) (1) = 764044478066980465818517510521751892567 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-5121) (-4865)) (2) = -149110292160451661557333053698632688307142157845 ∧
    lowLinearRadius (Finset.Ico (-5121) (-4865)) (2) = 763891431232182359012451374684904485423 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache11264
