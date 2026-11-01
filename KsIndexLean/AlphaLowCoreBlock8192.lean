module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate8192

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache8192
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-8193) (-7937)) n =
      blockLinearNumerator (-8193) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-8193) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 8192 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+8192 = -8193 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-8193) (-7937)) n =
      blockLinearRadius (-8193) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-8193) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 8192 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+8192 = -8193 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-8193) (-7937)) (-2) = -80388591140919031292233264481548658599462136436 ∧
    lowLinearRadius (Finset.Ico (-8193) (-7937)) (-2) = 366011427142660065645540396879315846019 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-8193) (-7937)) (-1) = 80378620392649238093399622816623480036815161073 ∧
    lowLinearRadius (Finset.Ico (-8193) (-7937)) (-1) = 365966029157366439570214205760013747786 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-8193) (-7937)) (1) = 80358686315036264486608822730686132655273219987 ∧
    lowLinearRadius (Finset.Ico (-8193) (-7937)) (1) = 365875266966690163099241228315795869305 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-8193) (-7937)) (2) = -80348722983853092938752851886717119148475472286 ∧
    lowLinearRadius (Finset.Ico (-8193) (-7937)) (2) = 365829902752929485777806437217158331422 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache8192
