module

public import KsIndexLean.DirichletLayerApproximation
public import KsIndexLean.L2MeasureRestriction
public import KsIndexLean.JacobiFamily
public import KsIndexLean.SingleDisk

@[expose] public section


/-!
# Collar convergence and support consequences of Dirichlet-layer approximation

The whole-plane convergence in `dirichlet_layer_approximation` restricts to
`Lp` convergence of values and directional derivatives on the collar
`annulusSet (1 / 2) 2`, as used by `localized_reflected_approximation`.
The approximants vanish on a neighborhood of the unit circle, with a positive
radius for each approximant. This also gives vanishing near every puncture
and near the points of any boundary arc.
-/

open Set MeasureTheory Filter Topology Metric
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Bracket KsIndex.SingleDisk

/-- Smooth approximants converge in collar `Lp` to the localized zero extension
and its weak derivative. Their support eventually lies in the seam domain,
and each approximant vanishes on a neighborhood of the entire unit circle. -/
theorem dirichlet_layer_approximation_frozen {A : Set Circle₁} (hA : IsOpen A)
    (u : ComplexH1) (hm : arcTrace A u = 0) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (seamDomain A hA : Set ℂ)) :
    let v := fun z => χ z • joinedDiskValue u 0 0 z
    let W := fun z => χ z • joinedDiskJet u 0 0 z +
      (fderiv ℝ χ z).smulRight (joinedDiskValue u 0 0 z)
    ∃ (hv : MemLp v 2 volume) (hW : ∀ d, MemLp (fun z => W z d) 2 volume),
    ∃ (f : ℕ → ℂ → ℂ)
      (hf : ∀ n, MemLp (f n) 2 volume)
      (hfD : ∀ n d, MemLp (fun z => fderiv ℝ (f n) z d) 2 volume),
      (∀ n, ContDiff ℝ ∞ (f n)) ∧
      (∀ n, ∃ δ : ℝ, 0 < δ ∧ ∀ w p : ℂ, ‖p‖ = 1 → ‖w - p‖ < δ → f n w = 0) ∧
      (∀ᶠ n in atTop, tsupport (f n) ⊆ (seamDomain A hA : Set ℂ)) ∧
      Tendsto (fun n =>
          ((hf n).mono_measure (Measure.restrict_le_self
            (s := annulusSet (1 / 2 : ℝ) 2))).toLp (f n))
        atTop (𝓝 ((hv.mono_measure (Measure.restrict_le_self
          (s := annulusSet (1 / 2 : ℝ) 2))).toLp v)) ∧
      ∀ d, Tendsto (fun n =>
          ((hfD n d).mono_measure (Measure.restrict_le_self
            (s := annulusSet (1 / 2 : ℝ) 2))).toLp
              (fun z => fderiv ℝ (f n) z d))
        atTop (𝓝 (((hW d).mono_measure (Measure.restrict_le_self
          (s := annulusSet (1 / 2 : ℝ) 2))).toLp (fun z => W z d))) := by
  dsimp only
  obtain ⟨hv, hW, f, hf, hfD, hsm, hvan, _hext, hsupp, hval, hjet⟩ :=
    dirichlet_layer_approximation hA u hm hχ hc hs
  refine ⟨hv, hW, f, hf, hfD, hsm, hvan, hsupp, ?_, ?_⟩
  · -- values: whole-plane toLp from the eLpNorm form, then restrict
    apply toLp_mono_measure_tendsto Measure.restrict_le_self hf hv
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hf _ hv]
    exact hval
  · intro d
    apply toLp_mono_measure_tendsto Measure.restrict_le_self
      (fun n => hfD n d) (hW d)
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun n => hfD n d) _ (hW d)]
    exact hjet d

/-- Uniform vanishing near the unit circle implies `SuppAwayP1` for `k ≥ 1`,
using the same positive radius for every puncture. -/
theorem dirichlet_layer_suppAwayP1 {k : ℕ} (hk : 1 ≤ k) {f : ℂ → ℂ}
    {δ : ℝ} (hδ : 0 < δ)
    (hvan : ∀ w p : ℂ, ‖p‖ = 1 → ‖w - p‖ < δ → f w = 0) :
    SuppAwayP1 k f := by
  refine ⟨δ, hδ, fun w hw => ?_⟩
  obtain ⟨p, hp, hwp⟩ := hw
  exact hvan w p (KsIndex.JacobiFamily.punctures_norm_eq_one hk hp) hwp

/-- Uniform vanishing near the unit circle gives vanishing near every point
of an arbitrary boundary arc, with the same positive radius. -/
lemma dirichlet_layer_vanish_on_arc {A : Set Circle₁} {f : ℂ → ℂ}
    {δ : ℝ} (hδ : 0 < δ)
    (hvan : ∀ w p : ℂ, ‖p‖ = 1 → ‖w - p‖ < δ → f w = 0) :
    ∃ δ' : ℝ, 0 < δ' ∧ ∀ w : ℂ,
      (∃ p : ℂ, (∃ q ∈ A, (q : ℂ) = p) ∧ ‖w - p‖ < δ') → f w = 0 := by
  refine ⟨δ, hδ, fun w ⟨p, ⟨q, _, hqp⟩, hwp⟩ => ?_⟩
  have hp : ‖p‖ = 1 := by
    rw [← hqp]
    exact mem_sphere_zero_iff_norm.mp q.property
  exact hvan w p hp hwp

end KsIndex.Trace
