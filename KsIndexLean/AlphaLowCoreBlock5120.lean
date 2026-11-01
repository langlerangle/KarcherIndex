module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate5120

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache5120
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-11265) (-11009)) n =
      blockLinearNumerator (-11265) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-11265) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 5120 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+5120 = -11265 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-11265) (-11009)) n =
      blockLinearRadius (-11265) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-11265) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 5120 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+5120 = -11265 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-11265) (-11009)) (-2) = -52763850565117218599879467272074782077122526040 ∧
    lowLinearRadius (Finset.Ico (-11265) (-11009)) (-2) = 223066025528461349298319469715696938090 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-11265) (-11009)) (-1) = 52759111950001655290652503736002646138021524394 ∧
    lowLinearRadius (Finset.Ico (-11265) (-11009)) (-1) = 223045992220676042073959056328428772288 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-11265) (-11009)) (1) = 52749637272817234574804307814797807888215014960 ∧
    lowLinearRadius (Finset.Ico (-11265) (-11009)) (1) = 223005936398654421828547133476142688608 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-11265) (-11009)) (2) = -52744901210289892362118252923211328141435243227 ∧
    lowLinearRadius (Finset.Ico (-11265) (-11009)) (2) = 222985913882479747493129351693412908186 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache5120
