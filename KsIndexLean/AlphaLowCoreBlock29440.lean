module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate29440

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache29440
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (13055) (13311)) n =
      blockLinearNumerator (13055) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (13055) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 29440 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+29440 = 13055 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (13055) (13311)) n =
      blockLinearRadius (13055) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (13055) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 29440 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+29440 = 13055 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (13055) (13311)) (-2) = 115784180941424292293127288847318591615312026305 ∧
    lowLinearRadius (Finset.Ico (13055) (13311)) (-2) = 172186610798987136398455281507490445188 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (13055) (13311)) (-1) = -115792963798402254739098813349984831729077927608 ∧
    lowLinearRadius (Finset.Ico (13055) (13311)) (-1) = 172199672109229427423294680815609405432 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (13055) (13311)) (1) = -115810533510453883268469064429765806968451362445 ∧
    lowLinearRadius (Finset.Ico (13055) (13311)) (1) = 172225800675440195178005940914375019406 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (13055) (13311)) (2) = 115819320366134279964287766607734741183658595376 ∧
    lowLinearRadius (Finset.Ico (13055) (13311)) (2) = 172238867932310966619018273725122954132 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache29440
