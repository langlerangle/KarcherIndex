module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate15872

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache15872
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-513) (-257)) n =
      blockLinearNumerator (-513) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-513) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 15872 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+15872 = -513 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-513) (-257)) n =
      blockLinearRadius (-513) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-513) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 15872 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+15872 = -513 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-513) (-257)) (-2) = -3245749297524216780583917315811828402285368387056 ∧
    lowLinearRadius (Finset.Ico (-513) (-257)) (-2) = 42898076232696682373034473904033519874051 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-513) (-257)) (-1) = 3236599374496522641937348276782465893325408937700 ∧
    lowLinearRadius (Finset.Ico (-513) (-257)) (-1) = 42774579155540491435912637688944144319432 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-513) (-257)) (1) = 3218459442409174247946492707699489744460831176444 ∧
    lowLinearRadius (Finset.Ico (-513) (-257)) (1) = 42529786564854625039102369753435696331768 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-513) (-257)) (2) = -3209468470772943507814096847546915856049187505654 ∧
    lowLinearRadius (Finset.Ico (-513) (-257)) (2) = 42408477558540938933394266873540537649181 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache15872
