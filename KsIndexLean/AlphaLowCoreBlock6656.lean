module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate6656

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache6656
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-9729) (-9473)) n =
      blockLinearNumerator (-9729) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-9729) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 6656 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+6656 = -9729 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-9729) (-9473)) n =
      blockLinearRadius (-9729) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-9729) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 6656 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+6656 = -9729 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-9729) (-9473)) (-2) = -64062899459903854243240043038392184088366916884 ∧
    lowLinearRadius (Finset.Ico (-9729) (-9473)) (-2) = 280093059964151491423532986224105859024 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-9729) (-9473)) (-1) = 64056225329652567326067353478909458976529416021 ∧
    lowLinearRadius (Finset.Ico (-9729) (-9473)) (-1) = 280063879222011525851461611493088881168 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-9729) (-9473)) (1) = 64042881240429203626834634948789141742505233547 ∧
    lowLinearRadius (Finset.Ico (-9729) (-9473)) (1) = 280005535975714799485620497974945656988 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-9729) (-9473)) (2) = -64036211280588160271876929756698008143114901577 ∧
    lowLinearRadius (Finset.Ico (-9729) (-9473)) (2) = 279976373467758625598221681811365387921 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache6656
