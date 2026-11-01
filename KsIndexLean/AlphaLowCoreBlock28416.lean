module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate28416

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache28416
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (12031) (12287)) n =
      blockLinearNumerator (12031) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (12031) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 28416 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+28416 = 12031 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (12031) (12287)) n =
      blockLinearRadius (12031) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (12031) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 28416 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+28416 = 12031 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (12031) (12287)) (-2) = 130455002849669614736438871700086604211657566015 ∧
    lowLinearRadius (Finset.Ico (12031) (12287)) (-2) = 194907957144239245758347976230234597360 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (12031) (12287)) (-1) = -130465732038150593496285993663475513365043260322 ∧
    lowLinearRadius (Finset.Ico (12031) (12287)) (-1) = 194923987258849317407474413260410356504 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (12031) (12287)) (1) = -130487195710670798309710567017699010334704298268 ∧
    lowLinearRadius (Finset.Ico (12031) (12287)) (1) = 194956055399999237002671149788829315054 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (12031) (12287)) (2) = 130497930195581363343871419800714160362656776503 ∧
    lowLinearRadius (Finset.Ico (12031) (12287)) (2) = 194972093427840928330867974227553258919 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache28416
