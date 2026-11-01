module

public import KsIndexLean.KarcherHeightStrip
public import KsIndexLean.KarcherHorizontalCoordinate
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section


/-! Strict monotonicity of the actual horizontal EW coordinate on height lines. -/
noncomputable section
namespace KsIndex.KarcherData
open Complex

def heightLineParameter (k : ℕ) (a s : ℝ) : ℂ :=
  heightSectorParameter k ((s : ℂ) + (a : ℂ) * I)

def heightLineY {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k) (a s : ℝ) : ℝ :=
  horizontalY hk b (heightLineParameter k a s)

lemma heightLine_mem_strip {a s : ℝ} (ha : 0 ≤ a) (hb : a ≤ Real.pi / 2)
    (hs : s ≤ 0) : heightStrip ((s : ℂ) + (a : ℂ) * I) := by
  simpa [heightStrip] using And.intro hs (And.intro ha hb)

lemma hasDerivAt_heightLineY {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k)
    {a s : ℝ} (ha : 0 ≤ a) (hb : a ≤ Real.pi / 2) (hs : s < 0) :
    HasDerivAt (heightLineY hk b a)
      (ewRealDifferential k (heightLineParameter k a s)
        (I * coeff3 k (heightLineParameter k a s))⁻¹).2.1 s := by
  have hζ := heightLine_mem_strip ha hb hs.le
  have hs' : ((s : ℂ) + (a : ℂ) * I).re < 0 := by simpa using hs
  have hp := hasDerivAt_heightStrip_parameter hk hζ hs'
  have hline : HasDerivAt (fun t : ℝ => (t : ℂ) + (a : ℂ) * I) 1 s :=
    Complex.ofRealCLM.hasDerivAt.add_const _
  have hd := (hp.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s hline
  have hy := hasFDerivAt_horizontalY hk b
    (heightStrip_parameter_not_puncture (by omega) hζ)
  convert hy.comp_hasDerivAt s hd using 1 <;>
    first | rfl | simp [heightLineParameter, ewRealDifferential,
      realCoeffLinear_apply]

lemma heightLineY_deriv_lower {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k)
    {a s : ℝ} (ha : 0 ≤ a) (hb : a ≤ Real.pi / 2) (hs : s < 0) :
    0 < Real.cos ((k - 1 : ℕ) * (Real.pi / (2 * k))) ∧
      Real.cos ((k - 1 : ℕ) * (Real.pi / (2 * k))) ≤ deriv (heightLineY hk b a) s := by
  rw [(hasDerivAt_heightLineY hk b ha hb hs).deriv]
  let w := heightLineParameter k a s
  have hζ := heightLine_mem_strip ha hb hs.le
  have hs' : ((s : ℂ) + (a : ℂ) * I).re < 0 := by simpa using hs
  have hw0 : w ≠ 0 := heightStrip_parameter_ne_zero (by omega) hζ hs'
  have harg := heightStrip_parameter_arg (by omega : k ≠ 0) hζ
  change 0 ≤ w.arg ∧ w.arg ≤ Real.pi / (2 * k) at harg
  have hp := ew_height_level_y_uniform hk (norm_pos_iff.mpr hw0) harg.1 harg.2
  have he : (‖w‖ : ℂ) * Complex.exp (w.arg * I) = w := Complex.norm_mul_exp_arg_mul_I w
  rw [he] at hp
  exact hp (heightStrip_parameter_not_puncture (by omega) hζ)

lemma heightLineY_continuousOn {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k)
    {a : ℝ} (ha : 0 ≤ a) (hb : a ≤ Real.pi / 2) :
    ContinuousOn (heightLineY hk b a) (Set.Iic 0) := by
  intro s hs
  have hζ := heightLine_mem_strip ha hb hs
  have hp := continuousAt_heightSectorParameter (by omega : k ≠ 0) hζ
  have hy := (hasFDerivAt_horizontalY hk b
    (heightStrip_parameter_not_puncture (by omega) hζ)).continuousAt
  have hl : ContinuousAt (fun t : ℝ => (t : ℂ) + (a : ℂ) * I) s := by fun_prop
  exact (hy.comp (f := fun t : ℝ => heightSectorParameter k ((t : ℂ) + (a : ℂ) * I))
    (hp.comp (f := fun t : ℝ => (t : ℂ) + (a : ℂ) * I) hl)).continuousWithinAt

/-- At a fixed height, distinct logarithmic radii have distinct horizontal
coordinates, including the right endpoint representing the sector boundary. -/
lemma heightLineY_strictMonoOn {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k)
    {a : ℝ} (ha : 0 ≤ a) (hb : a ≤ Real.pi / 2) :
    StrictMonoOn (heightLineY hk b a) (Set.Iic 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Iic 0) (heightLineY_continuousOn hk b ha hb)
  intro s hs
  rw [interior_Iic] at hs
  exact lt_of_lt_of_le (heightLineY_deriv_lower hk b ha hb hs).1
    (heightLineY_deriv_lower hk b ha hb hs).2

/-- The horizontal coordinate and logarithmic height jointly separate strip points. -/
lemma heightStrip_Y_im_injective {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k) :
    Set.InjOn (fun ζ : ℂ => (horizontalY hk b (heightSectorParameter k ζ), ζ.im))
      {ζ | heightStrip ζ} := by
  intro ζ hζ ξ hξ he
  have ha : ζ.im = ξ.im := congrArg Prod.snd he
  have hy := congrArg Prod.fst he
  have hz : (ζ.re : ℂ) + (ζ.im : ℂ) * I = ζ := Complex.re_add_im ζ
  have hx : (ξ.re : ℂ) + (ζ.im : ℂ) * I = ξ := by rw [ha]; exact Complex.re_add_im ξ
  have hr : ζ.re = ξ.re := by
    apply (heightLineY_strictMonoOn hk b hζ.2.1 hζ.2.2).injOn hζ.1 hξ.1
    simpa only [heightLineY, heightLineParameter, hz, hx] using hy
  exact Complex.ext hr ha

/-- A quantitative form of the monotonicity: horizontal displacement controls
logarithmic distance toward the puncture. -/
lemma heightLineY_displacement_lower {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k)
    {a s t : ℝ} (ha : 0 ≤ a) (hb : a ≤ Real.pi / 2)
    (hs : s ≤ 0) (ht : t ≤ 0) (hst : s ≤ t) :
    Real.cos ((k - 1 : ℕ) * (Real.pi / (2 * k))) * (t - s) ≤
      heightLineY hk b a t - heightLineY hk b a s := by
  let c := Real.cos ((k - 1 : ℕ) * (Real.pi / (2 * k)))
  have hm : MonotoneOn (fun u => heightLineY hk b a u - c * u) (Set.Iic 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Iic 0)
    · exact (heightLineY_continuousOn hk b ha hb).sub (continuousOn_const.mul continuousOn_id)
    · intro u hu
      rw [interior_Iic] at hu
      exact ((hasDerivAt_heightLineY hk b ha hb hu).sub
        ((hasDerivAt_id u).const_mul c)).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Iic] at hu
      have hd := ((hasDerivAt_heightLineY hk b ha hb hu).sub
        ((hasDerivAt_id u).const_mul c)).deriv
      change deriv (heightLineY hk b a - fun y => c * id y) u ≥ 0
      rw [hd]
      have hbound := (heightLineY_deriv_lower hk b ha hb hu).2
      rw [(hasDerivAt_heightLineY hk b ha hb hu).deriv] at hbound
      dsimp [c]
      linarith
  have hh := hm hs ht hst
  dsimp only at hh
  change c * (t - s) ≤ _
  linarith

end KsIndex.KarcherData
