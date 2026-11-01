module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate21504

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache21504
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (5119) (5375)) n =
      blockLinearNumerator (5119) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (5119) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 21504 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+21504 = 5119 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (5119) (5375)) n =
      blockLinearRadius (5119) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (5119) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 21504 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+21504 = 5119 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (5119) (5375)) (-2) = 451535891637977307516305081725557360118845854494 ∧
    lowLinearRadius (Finset.Ico (5119) (5375)) (-2) = 707866039146905404030131259623888833640 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (5119) (5375)) (-1) = -451621973567957698616198655181238347177853911708 ∧
    lowLinearRadius (Finset.Ico (5119) (5375)) (-1) = 708000990020230293244455086015388301440 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (5119) (5375)) (1) = -451794235950272127933008005103148377373002767914 ∧
    lowLinearRadius (Finset.Ico (5119) (5375)) (1) = 708271046222383254698670444211153910029 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (5119) (5375)) (2) = 451880416440207681070241712087303365251071425659 ∧
    lowLinearRadius (Finset.Ico (5119) (5375)) (2) = 708406151610160654180052998144509048022 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache21504
