module

public import KsIndexLean.KarcherChartTopology

@[expose] public section


/-! Continuity of the actual EW integral on the punctured parameter sphere,
including its regular infinity point. -/
noncomputable section
open scoped Topology ContDiff
namespace KsIndex.KarcherData

/-- Exact infinity chart identification supplies continuity of the one global map. -/
theorem continuous_extendedEWMap {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k)
    {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1) {X : ℂ → AmbientTriple} {C : PeriodTarget}
    (hzero : X 0 = 0) (hs : ContinuousOn X (Metric.ball (0 : ℂ) r))
    (hrep : ∀ v : infinityOverlap r,
      descendedIntegral hk b (infinityOverlapPoint hk hr v) = C + projectPeriod (X v.val)) :
    Continuous (extendedEWMap hk b C) := by
  have hf : Continuous (extendedEWMap hk b C ∘ finiteParameter) := by
    have he : extendedEWMap hk b C ∘ finiteParameter = descendedIntegral hk b :=
      funext (fun w => extendedEWMap_finite hk b w C)
    rw [he]
    exact continuous_descendedIntegral hk b
  have hi : Continuous (extendedEWMap hk b C ∘ infinityParameterChart hk hr) := by
    have he : extendedEWMap hk b C ∘ infinityParameterChart hk hr =
        (fun v : Metric.ball (0 : ℂ) r => C + projectPeriod (X v.val)) :=
      funext (extendedEWMap_infinityChart hk b hr hzero hrep)
    rw [he]
    exact continuous_const.add (continuous_projectPeriod.comp
      (hs.comp_continuous continuous_subtype_val (fun v => v.property)))
  rw [continuous_iff_continuousAt]
  intro p
  rcases parameterSphere_chart_cover hk hr0 hr p with ⟨w, rfl⟩ | ⟨v, rfl⟩
  · exact (isOpenEmbedding_finiteParameter k).continuousAt_iff.mp hf.continuousAt
  · exact (isOpenEmbedding_infinityParameterChart hk hr).continuousAt_iff.mp hi.continuousAt

/-- Existence of a continuous global EW map, agreeing with the actual finite
integral and regular at infinity. -/
theorem exists_continuous_extendedEWMap {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k) :
    ∃ C : PeriodTarget, Continuous (extendedEWMap hk b C) ∧
      (∀ w : PuncturedPlane k,
        extendedEWMap hk b C (finiteParameter w) = descendedIntegral hk b w) ∧
      extendedEWMap hk b C (infinityParameter k) = C := by
  obtain ⟨r, hr0, hr1, X, C, hz, hs, _, _, _, he, _⟩ := exists_curvature_infinity_chart hk b
  exact ⟨C, continuous_extendedEWMap hk b hr0 hr1.le hz hs.continuousOn he,
    fun w => extendedEWMap_finite hk b w C, extendedEWMap_infinity hk b C⟩

/-- The value at infinity does not depend on the chosen normalized primitive
or its radius. This is uniqueness of the constructed extension, not uniqueness
of the minimal surface among other surfaces. -/
theorem infinity_constant_unique {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k)
    {r s : ℝ} (hr0 : 0 < r) (hs0 : 0 < s) (hr : r ≤ 1) (hs : s ≤ 1)
    {X Y : ℂ → AmbientTriple} {C D : PeriodTarget} (hX0 : X 0 = 0) (hY0 : Y 0 = 0)
    (hX : ∀ z ∈ Metric.ball (0 : ℂ) r, HasFDerivAt X (infinityRealDifferential k z) z)
    (hY : ∀ z ∈ Metric.ball (0 : ℂ) s, HasFDerivAt Y (infinityRealDifferential k z) z)
    (hC : ∀ v : infinityOverlap r,
      descendedIntegral hk b (infinityOverlapPoint hk hr v) = C + projectPeriod (X v.val))
    (hD : ∀ v : infinityOverlap s,
      descendedIntegral hk b (infinityOverlapPoint hk hs v) = D + projectPeriod (Y v.val)) : C = D := by
  let t := min r s
  have ht : 0 < t := lt_min hr0 hs0
  have hsubr : Metric.ball (0 : ℂ) t ⊆ Metric.ball 0 r := Metric.ball_subset_ball (min_le_left _ _)
  have hsubs : Metric.ball (0 : ℂ) t ⊆ Metric.ball 0 s := Metric.ball_subset_ball (min_le_right _ _)
  have hd : ∀ z ∈ Metric.ball (0 : ℂ) t,
      HasFDerivAt (fun w => X w - Y w) (0 : ℂ →L[ℝ] AmbientTriple) z := by
    intro z hz
    convert (hX z (hsubr hz)).sub (hY z (hsubs hz)) using 1 <;> first | rfl | simp
  have hxy : ∀ z ∈ Metric.ball (0 : ℂ) t, X z = Y z := by
    intro z hz
    have he := Metric.isOpen_ball.is_const_of_fderiv_eq_zero
      (convex_ball (0 : ℂ) t).isPreconnected
      (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hd w hw).fderiv) hz (Metric.mem_ball_self ht)
    apply sub_eq_zero.mp
    simpa [hX0, hY0] using he
  let z : ℂ := (t / 2 : ℝ)
  have hz0 : z ≠ 0 := by
    change ((t / 2 : ℝ) : ℂ) ≠ 0
    exact_mod_cast (ne_of_gt (half_pos ht))
  have hz : ‖z‖ < t := by
    simp only [z, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos ht)]
    exact half_lt_self ht
  let vr : infinityOverlap r := ⟨z, hz0, hz.trans_le (min_le_left _ _)⟩
  let vs : infinityOverlap s := ⟨z, hz0, hz.trans_le (min_le_right _ _)⟩
  have hp : infinityOverlapPoint hk hr vr = infinityOverlapPoint hk hs vs := Subtype.ext rfl
  have he := (hC vr).symm.trans ((congrArg (descendedIntegral hk b) hp).trans (hD vs))
  change C + projectPeriod (X z) = D + projectPeriod (Y z) at he
  rw [hxy z (by simpa only [Metric.mem_ball, dist_zero_right] using hz)] at he
  exact add_right_cancel he

end KsIndex.KarcherData
