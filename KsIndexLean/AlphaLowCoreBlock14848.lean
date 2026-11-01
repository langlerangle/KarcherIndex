module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate14848

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache14848
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-1537) (-1281)) n =
      blockLinearNumerator (-1537) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-1537) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 14848 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+14848 = -1537 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-1537) (-1281)) n =
      blockLinearRadius (-1537) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-1537) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 14848 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+14848 = -1537 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-1537) (-1281)) (-2) = -724204346040147838613248700658407332147975035281 ∧
    lowLinearRadius (Finset.Ico (-1537) (-1281)) (-2) = 5383302905197187307890835280221077006944 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-1537) (-1281)) (-1) = 723686851852990003832200492356392096950560968057 ∧
    lowLinearRadius (Finset.Ico (-1537) (-1281)) (-1) = 5379452568467454648813551702423983165799 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-1537) (-1281)) (1) = 722654085136248042175670778879015432021400715862 ∧
    lowLinearRadius (Finset.Ico (-1537) (-1281)) (1) = 5371768440268263939925044348138087065716 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-1537) (-1281)) (2) = -722138809420964954779619515855425616602864729181 ∧
    lowLinearRadius (Finset.Ico (-1537) (-1281)) (2) = 5367934625052221630435152751660582236671 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache14848
