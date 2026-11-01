module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate27648

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache27648
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (11263) (11519)) n =
      blockLinearNumerator (11263) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (11263) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 27648 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+27648 = 11263 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (11263) (11519)) n =
      blockLinearRadius (11263) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (11263) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 27648 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+27648 = 11263 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (11263) (11519)) (-2) = 143640448082337563001105607747913887746460390624 ∧
    lowLinearRadius (Finset.Ico (11263) (11519)) (-2) = 215413811231681827317699225074050197144 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (11263) (11519)) (-1) = -143653058283822343263468975955186934847670393988 ∧
    lowLinearRadius (Finset.Ico (11263) (11519)) (-1) = 215432722465696906942178038986305708783 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (11263) (11519)) (1) = -143678285330539022132862351185569568563170807264 ∧
    lowLinearRadius (Finset.Ico (11263) (11519)) (1) = 215470554897228469817644840380488728896 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (11263) (11519)) (2) = 143690902176937836021531783728721285054380550063 ∧
    lowLinearRadius (Finset.Ico (11263) (11519)) (2) = 215489476096494957989373579835601548308 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache27648
