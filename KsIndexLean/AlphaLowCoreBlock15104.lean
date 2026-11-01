module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate15104

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache15104
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-1281) (-1025)) n =
      blockLinearNumerator (-1281) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-1281) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 15104 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+15104 = -1281 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-1281) (-1025)) n =
      blockLinearRadius (-1281) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-1281) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 15104 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+15104 = -1281 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-1281) (-1025)) (-2) = -921841669569491137545358879510842267733998205148 ∧
    lowLinearRadius (Finset.Ico (-1281) (-1025)) (-2) = 7353239509169824189683240747508086747065 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-1281) (-1025)) (-1) = 921034184890024149876740117928249212408454515475 ∧
    lowLinearRadius (Finset.Ico (-1281) (-1025)) (-1) = 7346788949864344483749275008675716951125 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-1281) (-1025)) (1) = 919423469475403612168465776603779639661639048457 ∧
    lowLinearRadius (Finset.Ico (-1281) (-1025)) (1) = 7333921863486638693033874233111422575864 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-1281) (-1025)) (2) = -918620231246185244909393029562391594931739884987 ∧
    lowLinearRadius (Finset.Ico (-1281) (-1025)) (2) = 7327505276373947245990036398432679046863 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache15104
