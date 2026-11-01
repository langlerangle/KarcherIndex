module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate9472

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache9472
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-6913) (-6657)) n =
      blockLinearNumerator (-6913) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-6913) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 9472 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+9472 = -6913 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-6913) (-6657)) n =
      blockLinearRadius (-6913) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-6913) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 9472 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+9472 = -6913 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-6913) (-6657)) (-2) = -100569523244804338793898230034167293238921006731 ∧
    lowLinearRadius (Finset.Ico (-6913) (-6657)) (-2) = 477236341513040074470029584985940649976 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-6913) (-6657)) (-1) = 100554694694022736152076015840874312236573609324 ∧
    lowLinearRadius (Finset.Ico (-6913) (-6657)) (-1) = 477165973005477523223918276450846354753 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-6913) (-6657)) (1) = 100525050708590241714277573000779151253782355573 ∧
    lowLinearRadius (Finset.Ico (-6913) (-6657)) (1) = 477025298234407219103239846713274652177 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-6913) (-6657)) (2) = -100510235270072307181933156131580438452488091931 ∧
    lowLinearRadius (Finset.Ico (-6913) (-6657)) (2) = 476954991952547457171834397864055376916 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache9472
