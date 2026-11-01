module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate7680

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache7680
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-8705) (-8449)) n =
      blockLinearNumerator (-8705) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-8705) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 7680 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+7680 = -8705 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-8705) (-8449)) n =
      blockLinearRadius (-8705) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-8705) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 7680 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+7680 = -8705 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-8705) (-8449)) (-2) = -74205903009032380683654850580010900944261902771 ∧
    lowLinearRadius (Finset.Ico (-8705) (-8449)) (-2) = 333016155501707935414530556463294090378 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-8705) (-8449)) (-1) = 74197248789829527943966806202851144377450493696 ∧
    lowLinearRadius (Finset.Ico (-8705) (-8449)) (-1) = 332977317017943606866121462874764909466 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-8705) (-8449)) (1) = 74179946406219985103621328019983935803135738078 ∧
    lowLinearRadius (Finset.Ico (-8705) (-8449)) (1) = 332899667223655115745676090135836811971 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-8705) (-8449)) (2) = -74171298240401305421031294109781844034045129234 ∧
    lowLinearRadius (Finset.Ico (-8705) (-8449)) (2) = 332860855906793993919011820221662837222 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache7680
