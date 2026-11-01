module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate6400

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache6400
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-9985) (-9729)) n =
      blockLinearNumerator (-9985) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-9985) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 6400 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+6400 = -9985 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-9985) (-9729)) n =
      blockLinearRadius (-9985) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-9985) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 6400 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+6400 = -9985 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-9985) (-9729)) (-2) = -61899446069750112358039497954410108356932219041 ∧
    lowLinearRadius (Finset.Ico (-9985) (-9729)) (-2) = 269010079886278441978158017955785301434 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-9985) (-9729)) (-1) = 61893164873428686562988254031629798754449734176 ∧
    lowLinearRadius (Finset.Ico (-9985) (-9729)) (-1) = 268982781955388400197467975270128220253 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-9985) (-9729)) (1) = 61880606304500705375741712759260414987086675002 ∧
    lowLinearRadius (Finset.Ico (-9985) (-9729)) (1) = 268928202711595972687576045253458671590 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-9985) (-9729)) (2) = -61874328931118282205240758336028267367438115321 ∧
    lowLinearRadius (Finset.Ico (-9985) (-9729)) (2) = 268900921395321597436972083535325077795 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache6400
