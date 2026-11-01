module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate12800

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache12800
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-3585) (-3329)) n =
      blockLinearNumerator (-3585) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-3585) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 12800 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+12800 = -3585 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-3585) (-3329)) n =
      blockLinearRadius (-3585) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-3585) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 12800 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+12800 = -3585 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-3585) (-3329)) (-2) = -238233980926870862635605595482912039530900487171 ∧
    lowLinearRadius (Finset.Ico (-3585) (-3329)) (-2) = 1345860747528822508242090154906453882387 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-3585) (-3329)) (-1) = 238164976094228821545316672374176036197207448829 ∧
    lowLinearRadius (Finset.Ico (-3585) (-3329)) (-1) = 1345470867832273631401258580013690715441 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-3585) (-3329)) (1) = 238027086338411572262660014719568117097879056553 ∧
    lowLinearRadius (Finset.Ico (-3585) (-3329)) (1) = 1344691786017034748785075501999209589838 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-3585) (-3329)) (2) = -237958201345769363695063434264092121359775715482 ∧
    lowLinearRadius (Finset.Ico (-3585) (-3329)) (2) = 1344302583505755119517867117512722350938 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache12800
