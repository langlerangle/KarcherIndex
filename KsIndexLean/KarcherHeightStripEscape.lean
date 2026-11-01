module

public import KsIndexLean.KarcherHeightLineMonotonicity

@[expose] public section


/-! Uniform escape toward the puncture in logarithmic sector coordinates. -/
noncomputable section
namespace KsIndex.KarcherData
open Complex Set

lemma heightStrip_horizontal_continuousOn {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k) :
    ContinuousOn (fun ζ => horizontalY hk b (heightSectorParameter k ζ)) {ζ | heightStrip ζ} := by
  intro ζ hζ
  have hp := continuousAt_heightSectorParameter (by omega : k ≠ 0) hζ
  have hy := (hasFDerivAt_horizontalY hk b
    (heightStrip_parameter_not_puncture (by omega) hζ)).continuousAt
  exact (hy.comp (f := heightSectorParameter k) hp).continuousWithinAt

lemma heightLineY_endpoint_bounded {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k) :
    ∃ M : ℝ, ∀ a ∈ Icc 0 (Real.pi / 2), heightLineY hk b a 0 ≤ M := by
  have hc : ContinuousOn (fun a => heightLineY hk b a 0) (Icc 0 (Real.pi / 2)) := by
    intro a ha
    have hζ := heightLine_mem_strip ha.1 ha.2 (le_refl (0 : ℝ))
    have hp := continuousAt_heightSectorParameter (by omega : k ≠ 0) hζ
    have hy := (hasFDerivAt_horizontalY hk b
      (heightStrip_parameter_not_puncture (by omega) hζ)).continuousAt
    have hl : ContinuousAt (fun a : ℝ => (0 : ℂ) + (a : ℂ) * I) a := by fun_prop
    exact (hy.comp (f := fun a : ℝ => heightSectorParameter k ((0 : ℂ) + (a : ℂ) * I))
      (hp.comp (f := fun a : ℝ => (0 : ℂ) + (a : ℂ) * I) hl)).continuousWithinAt
  obtain ⟨a, ha, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (by positivity : (0 : ℝ) ≤ Real.pi / 2)) hc
  exact ⟨heightLineY hk b a 0, fun t ht => hmax ht⟩

/-- The bound is uniform in the strip angle, including both edges. -/
lemma heightStrip_uniform_escape_bound {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k) :
    ∃ M : ℝ, ∀ ζ, heightStrip ζ →
      horizontalY hk b (heightSectorParameter k ζ) ≤
        M + Real.cos ((k - 1 : ℕ) * (Real.pi / (2 * k))) * ζ.re := by
  obtain ⟨M, hM⟩ := heightLineY_endpoint_bounded hk b
  refine ⟨M, ?_⟩
  intro ζ hζ
  have hd := heightLineY_displacement_lower hk b hζ.2.1 hζ.2.2 hζ.1 (le_refl 0) hζ.1
  have hm := hM ζ.im hζ.2
  have he : heightLineY hk b ζ.im ζ.re = horizontalY hk b (heightSectorParameter k ζ) := by
    unfold heightLineY heightLineParameter
    rw [Complex.re_add_im]
  rw [he] at hd
  linarith

/-- Any lower bound on horizontal position imposes a uniform lower bound on
the logarithmic radius. Thus sequences going to the end cannot stay bounded. -/
lemma heightStrip_bounded_position_bounds_radius {k : ℕ} (hk : 2 ≤ k)
    (b : PuncturedPlane k) (L : ℝ) :
    ∃ S : ℝ, ∀ ζ, heightStrip ζ → L ≤ horizontalY hk b (heightSectorParameter k ζ) →
      S ≤ ζ.re := by
  obtain ⟨M, hM⟩ := heightStrip_uniform_escape_bound hk b
  let c := Real.cos ((k - 1 : ℕ) * (Real.pi / (2 * k)))
  have hc : 0 < c := (heightLineY_deriv_lower hk b (a := 0) (s := -1)
    (le_refl 0) (by positivity) (by norm_num)).1
  refine ⟨(L - M) / c, ?_⟩
  intro ζ hζ hL
  apply (div_le_iff₀ hc).mpr
  have hh := hM ζ hζ
  change _ ≤ M + c * ζ.re at hh
  nlinarith

end KsIndex.KarcherData
