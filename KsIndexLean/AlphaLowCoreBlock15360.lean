module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate15360

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache15360
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-1025) (-769)) n =
      blockLinearNumerator (-1025) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-1025) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 15360 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+15360 = -1025 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-1025) (-769)) n =
      blockLinearRadius (-1025) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-1025) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 15360 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+15360 = -1025 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-1025) (-769)) (-2) = -1241642143522550698672608919891157235013289939468 ∧
    lowLinearRadius (Finset.Ico (-1025) (-769)) (-2) = 10890001921045591416424741124935478686643 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-1025) (-769)) (-1) = 1240235657079420639713718000343517373923304344332 ∧
    lowLinearRadius (Finset.Ico (-1025) (-769)) (-1) = 10877633573426418851810138405289439335797 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-1025) (-769)) (1) = 1237432287158678595440817432520211975815360600925 ∧
    lowLinearRadius (Finset.Ico (-1025) (-769)) (1) = 10852981544739622826242029244601579805898 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-1025) (-769)) (2) = -1236035381703695150552066042478323021850561868241 ∧
    lowLinearRadius (Finset.Ico (-1025) (-769)) (2) = 10840697669408635629411840806849354792890 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache15360
