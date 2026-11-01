module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache7680

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache7680
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-8705 : ℤ)+i.val) : ℝ) *
        sample (2*((-8705 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-8705) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-8705) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 7680 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+7680 = -8705 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+7680 = -8705 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-8705) (-2) center = -74205903009032380683654850580010900944261902771 ∧ blockLinearRadius (-8705) (-2) radius = 333016155501707935414530556463294090378 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-8705) (-1) center = 74197248789829527943966806202851144377450493696 ∧ blockLinearRadius (-8705) (-1) radius = 332977317017943606866121462874764909466 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-8705) (1) center = 74179946406219985103621328019983935803135738078 ∧ blockLinearRadius (-8705) (1) radius = 332899667223655115745676090135836811971 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-8705) (2) center = -74171298240401305421031294109781844034045129234 ∧ blockLinearRadius (-8705) (2) radius = 332860855906793993919011820221662837222 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache7680
