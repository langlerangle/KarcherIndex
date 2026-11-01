module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate30208

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache30208
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (13823) (14079)) n =
      blockLinearNumerator (13823) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (13823) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 30208 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+30208 = 13823 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (13823) (14079)) n =
      blockLinearRadius (13823) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (13823) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 30208 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+30208 = 13823 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (13823) (14079)) (-2) = 106505937153008533354475648442603657947089208681 ∧
    lowLinearRadius (Finset.Ico (13823) (14079)) (-2) = 157873635284717122917375358584235922191 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (13823) (14079)) (-1) = -106513571422887720281536080485078874337184982450 ∧
    lowLinearRadius (Finset.Ico (13823) (14079)) (-1) = 157884951572954154841145256623858103409 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (13823) (14079)) (1) = -106528843246523245257280378134282329588269730971 ∧
    lowLinearRadius (Finset.Ico (13823) (14079)) (1) = 157907589017131476108179938978888672172 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (13823) (14079)) (2) = 106536480800750482954043202206323719553096857016 ∧
    lowLinearRadius (Finset.Ico (13823) (14079)) (2) = 157918910173769782869626223275937926285 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache30208
