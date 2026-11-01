module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate3072

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache3072
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-13313) (-13057)) n =
      blockLinearNumerator (-13313) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-13313) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 3072 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+3072 = -13313 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-13313) (-13057)) n =
      blockLinearRadius (-13313) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-13313) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 3072 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+3072 = -13313 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-13313) (-13057)) (-2) = -42278428551831569922242879876074051416072696604 ∧
    lowLinearRadius (Finset.Ico (-13313) (-13057)) (-2) = 172194462255428423673890933107535730956 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-13313) (-13057)) (-1) = 42275221520301752695609928558935007008537892932 ∧
    lowLinearRadius (Finset.Ico (-13313) (-13057)) (-1) = 172181400349591082196446980263028819862 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-13313) (-13057)) (1) = 42268808916683421014552039409571334788883686042 ∧
    lowLinearRadius (Finset.Ico (-13313) (-13057)) (1) = 172155282482109730879945116445028270696 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-13313) (-13057)) (2) = -42265603344373531097666618414656362237228410743 ∧
    lowLinearRadius (Finset.Ico (-13313) (-13057)) (2) = 172142226519564069459375049115464226429 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache3072
