module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate21248

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache21248
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (4863) (5119)) n =
      blockLinearNumerator (4863) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (4863) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 21248 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+21248 = 4863 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (4863) (5119)) n =
      blockLinearRadius (4863) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (4863) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 21248 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+21248 = 4863 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (4863) (5119)) (-2) = 486219148794388409079393695711716436247362020713 ∧
    lowLinearRadius (Finset.Ico (4863) (5119)) (-2) = 764412892560544322419007832399310853211 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (4863) (5119)) (-1) = -486316601413874367340089921383588375169224022277 ∧
    lowLinearRadius (Finset.Ico (4863) (5119)) (-1) = 764566105300149413190234822450538062115 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (4863) (5119)) (1) = -486511623919792713659786891420109037993310399395 ∧
    lowLinearRadius (Finset.Ico (4863) (5119)) (1) = 764872715146022123710477214524917263301 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (4863) (5119)) (2) = 486609193853281515096529470274295479275243200175 ∧
    lowLinearRadius (Finset.Ico (4863) (5119)) (2) = 765026112326272586040573934489503607042 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache21248
