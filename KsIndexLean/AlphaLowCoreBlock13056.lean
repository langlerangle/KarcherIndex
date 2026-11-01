module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate13056

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache13056
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-3329) (-3073)) n =
      blockLinearNumerator (-3329) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-3329) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 13056 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+13056 = -3329 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-3329) (-3073)) n =
      blockLinearRadius (-3329) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-3329) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 13056 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+13056 = -3329 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-3329) (-3073)) (-2) = -262522405825711532856281832200183153668904066513 ∧
    lowLinearRadius (Finset.Ico (-3329) (-3073)) (-2) = 1515140022463813927834166916312567990578 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-3329) (-3073)) (-1) = 262440268633688204073780837930371863905508555122 ∧
    lowLinearRadius (Finset.Ico (-3329) (-3073)) (-1) = 1514665899433760133786837503615725688689 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-3329) (-3073)) (1) = 262276148428330100169007830328366572664856428736 ∧
    lowLinearRadius (Finset.Ico (-3329) (-3073)) (1) = 1513718543476634251216984331723500037565 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-3329) (-3073)) (2) = -262194165318505219468868357472659952487020992184 ∧
    lowLinearRadius (Finset.Ico (-3329) (-3073)) (2) = 1513245309992423518652664869180602549776 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache13056
