module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate27136

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache27136
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (10751) (11007)) n =
      blockLinearNumerator (10751) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (10751) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 27136 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+27136 = 10751 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (10751) (11007)) n =
      blockLinearRadius (10751) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (10751) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 27136 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+27136 = 10751 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (10751) (11007)) (-2) = 153728961013297509970187190496512156634257355502 ∧
    lowLinearRadius (Finset.Ico (10751) (11007)) (-2) = 231152947342886924225455063847656850726 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (10751) (11007)) (-1) = -153743092127639550503489280174696584987997392988 ∧
    lowLinearRadius (Finset.Ico (10751) (11007)) (-1) = 231174195501723429698971366150422977299 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (10751) (11007)) (1) = -153771362151900776655503595910735323123095274071 ∧
    lowLinearRadius (Finset.Ico (10751) (11007)) (1) = 231216703541196730256478435585478340464 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (10751) (11007)) (2) = 153785501063253664172444723985064438607046826088 ∧
    lowLinearRadius (Finset.Ico (10751) (11007)) (2) = 231237963423989313363484049067935235198 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache27136
