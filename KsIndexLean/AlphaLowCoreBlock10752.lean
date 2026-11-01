module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate10752

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache10752
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-5633) (-5377)) n =
      blockLinearNumerator (-5633) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-5633) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 10752 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+10752 = -5633 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-5633) (-5377)) n =
      blockLinearRadius (-5633) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-5633) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 10752 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+10752 = -5633 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-5633) (-5377)) (-2) = -131667492231537428240191947859984605368348226151 ∧
    lowLinearRadius (Finset.Ico (-5633) (-5377)) (-2) = 657984951679782432434297930747630827810 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-5633) (-5377)) (-1) = 131643560231176627352265105064320450024591045363 ∧
    lowLinearRadius (Finset.Ico (-5633) (-5377)) (-1) = 657865350317270428174178904732134564680 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-5633) (-5377)) (1) = 131595722325081771014248679044547170679960063714 ∧
    lowLinearRadius (Finset.Ico (-5633) (-5377)) (1) = 657626278007362387313005094708866344977 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-5633) (-5377)) (2) = -131571816409863504807796638960251869728980263488 ∧
    lowLinearRadius (Finset.Ico (-5633) (-5377)) (2) = 657506807012564233302353127486862748269 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache10752
