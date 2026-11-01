module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate2048

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache2048
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-14337) (-14081)) n =
      blockLinearNumerator (-14337) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-14337) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 2048 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+2048 = -14337 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-14337) (-14081)) n =
      blockLinearRadius (-14337) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-14337) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 2048 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+2048 = -14337 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-14337) (-14081)) (-2) = -38314971325863209696463049826933938643321157568 ∧
    lowLinearRadius (Finset.Ico (-14337) (-14081)) (-2) = 153541432019310507331287543015032817719 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-14337) (-14081)) (-1) = 38312274438673580876778694006987272053796586350 ∧
    lowLinearRadius (Finset.Ico (-14337) (-14081)) (-1) = 153530624590211747635807007685220796862 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-14337) (-14081)) (1) = 38306881803124375575602373764452219770714405535 ∧
    lowLinearRadius (Finset.Ico (-14337) (-14081)) (1) = 153509014295756033751057455570326575110 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-14337) (-14081)) (2) = -38304186054604505936999602804103148481994565539 ∧
    lowLinearRadius (Finset.Ico (-14337) (-14081)) (2) = 153498211429756717827797756347312923525 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache2048
