module

public import KsIndexLean.KaiStage2Probe
public import KsIndexLean.KaiStage2GrpAe
public import KsIndexLean.KaiStage2GrpBo
public import KsIndexLean.KaiStage2GrpBe
public import KsIndexLean.KaiStage2GrpAoNeg
public import KsIndexLean.KaiStage2GrpBoNeg
public import KsIndexLean.KaiStage2GrpAeNeg
public import KsIndexLean.KaiStage2GrpBeNeg

@[expose] public section


/-! Conditional outer raw-remainder bounds on both frequency sides.

For every natural number `m > 1025`, the two theorems bound the absolute
value of `rawRemainder m` and `rawRemainderNegative m` by `1/m`.
They assume interval bounds for the two positive seed ratios and for
`Upos` or `Uneg`, together with the displayed endpoint inequalities
`hcond_lo` and `hcond_hi`.

Four group identities on each side express the scaled remainder as a
sum of enclosed group values, two multiplied by seed ratios, plus
`m*Upos/(6*m+1)` or `m*Uneg/(6*m-1)`. The rational group enclosures apply
for `m ≥ 1024`. For `m ≥ 1`, the remaining factors lie in `[1/7,1/6]`
and `[1/6,1/5]`, respectively. Sign-aware multiplication of the interval
bounds gives a scaled remainder in `[-1,1]`, and division by positive
`m` yields the result. The seed and U interval bounds and endpoint
inequalities remain explicit hypotheses of these theorems.
-/
noncomputable section
namespace KsIndex.Stage3Outer
open KsIndex.CircleQ KsIndex.PowerArc KsIndex.OppositeHalf KsIndex.AlphaRemarkTrial
open KsIndex.Stage2Probe KsIndex.Stage2GrpAe KsIndex.Stage2GrpBo KsIndex.Stage2GrpBe

set_option linter.style.longLine false
set_option maxHeartbeats 1600000

/-- Conditional outer bound on the positive raw remainder. `seedA = g β_A 1/g β_A 0`,
`seedB = g β_B 1/g β_B 0`; seed and U interval bounds and the two
endpoint inequalities are explicit hypotheses. -/
theorem rawRemainder_outer_le
    (sAl sAh sBl sBh Ul Uh : ℝ)
    (hsAl : sAl ≤ g (2161809/5000000:ℝ) 1 / g (2161809/5000000:ℝ) 0)
    (hsAh : g (2161809/5000000:ℝ) 1 / g (2161809/5000000:ℝ) 0 ≤ sAh) (hsAl0 : 0 ≤ sAl)
    (hsBl : sBl ≤ g (2838191/5000000:ℝ) 1 / g (2838191/5000000:ℝ) 0)
    (hsBh : g (2838191/5000000:ℝ) 1 / g (2838191/5000000:ℝ) 0 ≤ sBh) (hsBl0 : 0 ≤ sBl)
    (hUl : Ul ≤ Upos) (hUh : Upos ≤ Uh) (hUl0 : 0 ≤ Ul)
    (hcond_hi : sAh*(89739/200000) + 974023/1000000 + sBl*(-478379/500000)
        + (-864827/500000) + Uh/6 ≤ 1)
    (hcond_lo : (-1:ℝ) ≤ sAl*(448651/1000000) + 23049/25000 + sBh*(-1065041/1000000)
        + (-1730299/1000000) + Ul/7) :
    ∀ m : ℕ, 1025 < m → |rawRemainder (m : ℝ)| ≤ 1 / (m : ℝ) := by
  intro m hm
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
  have hm3 : (3:ℝ) ≤ (m:ℝ) := by exact_mod_cast (by omega : 3 ≤ m)
  have hm1024 : (1024:ℝ) ≤ (m:ℝ) := by exact_mod_cast (by omega : 1024 ≤ m)
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hden6 : (0:ℝ) < 6*(m:ℝ)+1 := by positivity
  -- grpValue enclosures
  have hg00 := GroupBounds.grp_bounds_0_0_p (m:ℝ) hm1024
  have hg01 := GroupBounds.grp_bounds_0_1_p (m:ℝ) hm1024
  have hg10 := GroupBounds.grp_bounds_1_0_p (m:ℝ) hm1024
  have hg11 := GroupBounds.grp_bounds_1_1_p (m:ℝ) hm1024
  -- key identity from the four positive bridges
  have key : (m:ℝ) * rawRemainder (m:ℝ)
      = g (2161809/5000000:ℝ) 1 / g (2161809/5000000:ℝ) 0 * GroupBounds.grpValue_0_0_p (m:ℝ)
        + GroupBounds.grpValue_0_1_p (m:ℝ)
        + g (2838191/5000000:ℝ) 1 / g (2838191/5000000:ℝ) 0 * GroupBounds.grpValue_1_0_p (m:ℝ)
        + GroupBounds.grpValue_1_1_p (m:ℝ)
        + (m:ℝ) * Upos / (6*(m:ℝ)+1) := by
    have e := rawRemainder_regrouped (m:ℝ) hm1
    have bAe := bridge_grpAe (m:ℝ) hm3
    have bAo := bridge_grpAo (m:ℝ) hm3
    have bBe := bridge_grpBe (m:ℝ) hm3
    have bBo := bridge_grpBo (m:ℝ) hm3
    rw [e]; linear_combination bAe + bAo + bBe + bBo
  -- product enclosures (grpAe: positive seed × positive grpValue)
  have h00nn : (0:ℝ) ≤ GroupBounds.grpValue_0_0_p (m:ℝ) := le_trans (by norm_num) hg00.1
  have pAe_hi : g (2161809/5000000:ℝ) 1 / g (2161809/5000000:ℝ) 0 * GroupBounds.grpValue_0_0_p (m:ℝ)
      ≤ sAh * (89739/200000) := mul_le_mul hsAh hg00.2 h00nn (le_trans hsAl0 (le_trans hsAl hsAh))
  have pAe_lo : sAl * (448651/1000000)
      ≤ g (2161809/5000000:ℝ) 1 / g (2161809/5000000:ℝ) 0 * GroupBounds.grpValue_0_0_p (m:ℝ) :=
    mul_le_mul hsAl hg00.1 (by norm_num) (le_trans hsAl0 hsAl)
  -- product enclosures (grpBe: positive seed × negative grpValue)
  have pBe_hi : g (2838191/5000000:ℝ) 1 / g (2838191/5000000:ℝ) 0 * GroupBounds.grpValue_1_0_p (m:ℝ)
      ≤ sBl * (-478379/500000) := by
    nlinarith [hsBl, hsBh, hsBl0, hg10.1, hg10.2,
      mul_nonneg (sub_nonneg.2 hsBl) (by linarith [hg10.2] : (0:ℝ) ≤ -GroupBounds.grpValue_1_0_p (m:ℝ)),
      mul_nonneg hsBl0 (by linarith [hg10.2] : (0:ℝ) ≤ -478379/500000 - GroupBounds.grpValue_1_0_p (m:ℝ))]
  have pBe_lo : sBh * (-1065041/1000000)
      ≤ g (2838191/5000000:ℝ) 1 / g (2838191/5000000:ℝ) 0 * GroupBounds.grpValue_1_0_p (m:ℝ) := by
    nlinarith [hsBl, hsBh, hsBl0, hg10.1, hg10.2,
      mul_nonneg (sub_nonneg.2 hsBh) (by linarith [hg10.2] : (0:ℝ) ≤ -GroupBounds.grpValue_1_0_p (m:ℝ)),
      mul_nonneg (le_trans hsBl0 (le_trans hsBl hsBh)) (by linarith [hg10.1] : (0:ℝ) ≤ GroupBounds.grpValue_1_0_p (m:ℝ) + 1065041/1000000)]
  -- m/(6m+1) ∈ [1/7, 1/6] scaled by U
  have hUh0 : (0:ℝ) ≤ Uh := le_trans hUl0 (le_trans hUl hUh)
  have ht_hi : (m:ℝ) * Upos / (6*(m:ℝ)+1) ≤ Uh/6 := by
    rw [div_le_iff₀ hden6]; nlinarith [hUh, hUl, hUl0, hUh0, hmpos, hm1,
      mul_le_mul_of_nonneg_left hUh hmpos.le]
  have ht_lo : Ul/7 ≤ (m:ℝ) * Upos / (6*(m:ℝ)+1) := by
    rw [le_div_iff₀ hden6]; nlinarith [hUl, hUl0, hmpos, hm1,
      mul_le_mul_of_nonneg_left hUl hmpos.le]
  -- assemble the two-sided bound on m·rawRemainder, then divide
  have hub : (m:ℝ) * rawRemainder (m:ℝ) ≤ 1 := by
    rw [key]; linarith [pAe_hi, hg01.2, pBe_hi, hg11.2, ht_hi, hcond_hi]
  have hlb : (-1:ℝ) ≤ (m:ℝ) * rawRemainder (m:ℝ) := by
    rw [key]; linarith [pAe_lo, hg01.1, pBe_lo, hg11.1, ht_lo, hcond_lo]
  rw [abs_le]
  constructor
  · rw [← neg_div, div_le_iff₀ hmpos]; nlinarith [hlb]
  · rw [le_div_iff₀ hmpos]; nlinarith [hub]

/-- Conditional outer bound on the negative raw remainder (reflected side). -/
theorem rawRemainderNegative_outer_le
    (sAl sAh sBl sBh Ul Uh : ℝ)
    (hsAl : sAl ≤ g (2161809/5000000:ℝ) 1 / g (2161809/5000000:ℝ) 0)
    (hsAh : g (2161809/5000000:ℝ) 1 / g (2161809/5000000:ℝ) 0 ≤ sAh) (hsAl0 : 0 ≤ sAl)
    (hsBl : sBl ≤ g (2838191/5000000:ℝ) 1 / g (2838191/5000000:ℝ) 0)
    (hsBh : g (2838191/5000000:ℝ) 1 / g (2838191/5000000:ℝ) 0 ≤ sBh) (hsBl0 : 0 ≤ sBl)
    (hUl : Ul ≤ Uneg) (hUh : Uneg ≤ Uh) (hUl0 : 0 ≤ Ul)
    (hcond_hi : sAl*(-428547/1000000) + (-1108049/1000000) + sBh*(537423/1000000)
        + (-132331/1000000) + Uh/5 ≤ 1)
    (hcond_lo : (-1:ℝ) ≤ sAh*(-42863/100000) + (-1160611/1000000) + sBl*(214639/500000)
        + (-2073/15625) + Ul/6) :
    ∀ m : ℕ, 1025 < m → |rawRemainderNegative (m : ℝ)| ≤ 1 / (m : ℝ) := by
  intro m hm
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
  have hm3 : (3:ℝ) ≤ (m:ℝ) := by exact_mod_cast (by omega : 3 ≤ m)
  have hm1024 : (1024:ℝ) ≤ (m:ℝ) := by exact_mod_cast (by omega : 1024 ≤ m)
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hden6 : (0:ℝ) < 6*(m:ℝ)-1 := by linarith [hm1]
  have hg00m := GroupBounds.grp_bounds_0_0_m (m:ℝ) hm1024
  have hg01m := GroupBounds.grp_bounds_0_1_m (m:ℝ) hm1024
  have hg10m := GroupBounds.grp_bounds_1_0_m (m:ℝ) hm1024
  have hg11m := GroupBounds.grp_bounds_1_1_m (m:ℝ) hm1024
  have key : (m:ℝ) * rawRemainderNegative (m:ℝ)
      = g (2161809/5000000:ℝ) 1 / g (2161809/5000000:ℝ) 0 * GroupBounds.grpValue_0_0_m (m:ℝ)
        + GroupBounds.grpValue_0_1_m (m:ℝ)
        + g (2838191/5000000:ℝ) 1 / g (2838191/5000000:ℝ) 0 * GroupBounds.grpValue_1_0_m (m:ℝ)
        + GroupBounds.grpValue_1_1_m (m:ℝ)
        + (m:ℝ) * Uneg / (6*(m:ℝ)-1) := by
    have e := rawRemainderNegative_regrouped (m:ℝ) hm1
    have bAe := KsIndex.Stage2GrpAeNeg.bridge_grpAe_neg (m:ℝ) hm3
    have bAo := KsIndex.Stage2GrpAoNeg.bridge_grpAo_neg (m:ℝ) hm3
    have bBe := KsIndex.Stage2GrpBeNeg.bridge_grpBe_neg (m:ℝ) hm3
    have bBo := KsIndex.Stage2GrpBoNeg.bridge_grpBo_neg (m:ℝ) hm3
    rw [e]; linear_combination bAe + bAo + bBe + bBo
  have pAe_hi : g (2161809/5000000:ℝ) 1 / g (2161809/5000000:ℝ) 0 * GroupBounds.grpValue_0_0_m (m:ℝ)
      ≤ sAl * (-428547/1000000) := by
    nlinarith [hsAl, hsAh, hsAl0, hg00m.1, hg00m.2,
      mul_nonneg (sub_nonneg.2 hsAl) (by linarith [hg00m.2] : (0:ℝ) ≤ -GroupBounds.grpValue_0_0_m (m:ℝ)),
      mul_nonneg hsAl0 (by linarith [hg00m.2] : (0:ℝ) ≤ -428547/1000000 - GroupBounds.grpValue_0_0_m (m:ℝ))]
  have pAe_lo : sAh * (-42863/100000)
      ≤ g (2161809/5000000:ℝ) 1 / g (2161809/5000000:ℝ) 0 * GroupBounds.grpValue_0_0_m (m:ℝ) := by
    nlinarith [hsAl, hsAh, hsAl0, hg00m.1, hg00m.2,
      mul_nonneg (sub_nonneg.2 hsAh) (by linarith [hg00m.2] : (0:ℝ) ≤ -GroupBounds.grpValue_0_0_m (m:ℝ)),
      mul_nonneg (le_trans hsAl0 (le_trans hsAl hsAh)) (by linarith [hg00m.1] : (0:ℝ) ≤ GroupBounds.grpValue_0_0_m (m:ℝ) + 42863/100000)]
  have pBe_hi : g (2838191/5000000:ℝ) 1 / g (2838191/5000000:ℝ) 0 * GroupBounds.grpValue_1_0_m (m:ℝ)
      ≤ sBh * (537423/1000000) :=
    mul_le_mul hsBh hg10m.2 (le_trans (by norm_num) hg10m.1) (le_trans hsBl0 (le_trans hsBl hsBh))
  have pBe_lo : sBl * (214639/500000)
      ≤ g (2838191/5000000:ℝ) 1 / g (2838191/5000000:ℝ) 0 * GroupBounds.grpValue_1_0_m (m:ℝ) :=
    mul_le_mul hsBl hg10m.1 (by norm_num) (le_trans hsBl0 hsBl)
  have hUh0 : (0:ℝ) ≤ Uh := le_trans hUl0 (le_trans hUl hUh)
  have ht_hi : (m:ℝ) * Uneg / (6*(m:ℝ)-1) ≤ Uh/5 := by
    rw [div_le_iff₀ hden6]; nlinarith [hUh, hUl, hUl0, hUh0, hmpos, hm1,
      mul_le_mul_of_nonneg_left hUh hmpos.le]
  have ht_lo : Ul/6 ≤ (m:ℝ) * Uneg / (6*(m:ℝ)-1) := by
    rw [le_div_iff₀ hden6]; nlinarith [hUl, hUl0, hmpos, hm1,
      mul_le_mul_of_nonneg_left hUl hmpos.le]
  have hub : (m:ℝ) * rawRemainderNegative (m:ℝ) ≤ 1 := by
    rw [key]; linarith [pAe_hi, hg01m.2, pBe_hi, hg11m.2, ht_hi, hcond_hi]
  have hlb : (-1:ℝ) ≤ (m:ℝ) * rawRemainderNegative (m:ℝ) := by
    rw [key]; linarith [pAe_lo, hg01m.1, pBe_lo, hg11m.1, ht_lo, hcond_lo]
  rw [abs_le]
  constructor
  · rw [← neg_div, div_le_iff₀ hmpos]; nlinarith [hlb]
  · rw [le_div_iff₀ hmpos]; nlinarith [hub]

end KsIndex.Stage3Outer

#print axioms KsIndex.Stage3Outer.rawRemainder_outer_le
#print axioms KsIndex.Stage3Outer.rawRemainderNegative_outer_le
