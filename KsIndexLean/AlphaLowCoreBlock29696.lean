module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate29696

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache29696
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (13311) (13567)) n =
      blockLinearNumerator (13311) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (13311) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 29696 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+29696 = 13311 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (13311) (13567)) n =
      blockLinearRadius (13311) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (13311) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 29696 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+29696 = 13311 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (13311) (13567)) (-2) = 112545246372589816540549842294074874578918764211 ∧
    lowLinearRadius (Finset.Ico (13311) (13567)) (-2) = 167184867441136711673602257657457645376 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (13311) (13567)) (-1) = -112553620901558124104870482462485492714299243419 ∧
    lowLinearRadius (Finset.Ico (13311) (13567)) (-1) = 167197307743992956776888998598822780400 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (13311) (13567)) (1) = -112570373699073149990608536217502836966567720069 ∧
    lowLinearRadius (Finset.Ico (13311) (13567)) (1) = 167222193904832076651965144982137686276 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (13311) (13567)) (2) = 112578751968176552777583617401197786287903235850 ∧
    lowLinearRadius (Finset.Ico (13311) (13567)) (2) = 167234639763641905089857925276921245333 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache29696
