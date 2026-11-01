module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate1024

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache1024
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-15361) (-15105)) n =
      blockLinearNumerator (-15361) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-15361) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 1024 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+1024 = -15361 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-15361) (-15105)) n =
      blockLinearRadius (-15361) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-15361) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 1024 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+1024 = -15361 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-15361) (-15105)) (-2) = -34956813461133474338280065541262032201858615243 ∧
    lowLinearRadius (Finset.Ico (-15361) (-15105)) (-2) = 138008863608947634831265885673273277585 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-15361) (-15105)) (-1) = 34954518376988533944009815956987210495935996691 ∧
    lowLinearRadius (Finset.Ico (-15361) (-15105)) (-1) = 137999802612994946084300330081259490141 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-15361) (-15105)) (1) = 34949929112701578155304258409763385851538506305 ∧
    lowLinearRadius (Finset.Ico (-15361) (-15105)) (1) = 137981684190112512123488403342364103511 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-15361) (-15105)) (2) = -34947634932440876209020415792998631811512015351 ∧
    lowLinearRadius (Finset.Ico (-15361) (-15105)) (2) = 137972626762714187504184381097112829164 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache1024
