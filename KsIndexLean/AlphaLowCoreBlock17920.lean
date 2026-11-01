module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate17920

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache17920
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (1535) (1791)) n =
      blockLinearNumerator (1535) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (1535) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 17920 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+17920 = 1535 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (1535) (1791)) n =
      blockLinearRadius (1535) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (1535) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 17920 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+17920 = 1535 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (1535) (1791)) (-2) = 2483198572520427951178795362718895793194712263336 ∧
    lowLinearRadius (Finset.Ico (1535) (1791)) (-2) = 4154305188337131193405054846885247927129 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (1535) (1791)) (-1) = -2484698230504993891032006291364278083411811137886 ∧
    lowLinearRadius (Finset.Ico (1535) (1791)) (-1) = 4156814341220122272354479983313585349144 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (1535) (1791)) (1) = -2487702997883143471977328549456660023646158208300 ∧
    lowLinearRadius (Finset.Ico (1535) (1791)) (1) = 4161841769016282942580589713035659334988 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (1535) (1791)) (2) = 2489208113899256620041014024385206982869525703481 ∧
    lowLinearRadius (Finset.Ico (1535) (1791)) (2) = 4164360055012373076334974291862396736170 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache17920
