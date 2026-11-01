module

public import KsIndexLean.DirichletLayerApproximation
public import KsIndexLean.SingleCcSlitClearance

@[expose] public section


/-!
# Dirichlet layer approximants in the single-disk core

The approximants from `dirichlet_layer_approximation` lie in
`SingleCc k b₁ false` for either arc-1 flag. Uniform vanishing near the
unit circle supplies the reflection germ, slit clearance, puncture clearance,
and odd-case circle condition. Vanishing on the closed exterior supplies the
remaining support conditions. The generic membership theorem isolates these
hypotheses before applying them to the convergent layer approximants.
-/

open Set MeasureTheory Filter Topology Metric
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Bracket KsIndex.SingleDisk

/-- Generic form: smoothness + uniform circle-neighborhood vanishing +
closed-exterior vanishing put a function in `SingleCc k b₁ false`, for
every `b₁`. -/
theorem singleCc_of_dirichlet_clauses {k : ℕ} (hk : 1 ≤ k) (b₁ : Bool)
    {f : ℂ → ℂ} (hsm : ContDiff ℝ ∞ f)
    {δ : ℝ} (hδ : 0 < δ)
    (hv : ∀ w p : ℂ, ‖p‖ = 1 → ‖w - p‖ < δ → f w = 0)
    (hext : ∀ w : ℂ, 1 ≤ ‖w‖ → f w = 0) :
    f ∈ SingleCc k b₁ false := by
  refine ⟨hsm.contDiffOn, ?_, ?_, ?_, ?_, ?_⟩
  · -- arc-1 germ: f dies on a δ-ball around each arc point, so the
    -- reflected function has the constant-zero germ there
    intro w hw
    have hze : f =ᶠ[𝓝 w] 0 := by
      filter_upwards [Metric.ball_mem_nhds w hδ] with z hz
      exact hv z w hw.1 (by simpa [dist_eq_norm] using hz)
    have hw0 : w ≠ 0 := by
      intro h
      subst h
      simpa using hw.1
    have ht : Tendsto σ (𝓝 w) (𝓝 w) := by
      simpa only [σ_self hw.1] using (continuousAt_σ hw0).tendsto
    have hr : refl (sgn b₁) f =ᶠ[𝓝 w] 0 := by
      filter_upwards [hze, ht.eventually hze] with z hz hi
      simp [KsIndex.SingleDisk.refl, hz, hi]
    exact contDiffAt_const.congr_of_eventuallyEq hr
  · -- Arc0Cond false = SuppAwaySlit1: slit points are circle points
    exact ⟨δ, hδ, fun w ⟨p, hp, hwp⟩ => hv w p hp.1 hwp⟩
  · exact fun w hw => hext w hw.le
  · exact fun _ w hw => hext w hw.ge
  · exact ⟨δ, hδ, fun w ⟨p, hp, hwp⟩ =>
      hv w p (KsIndex.JacobiFamily.punctures_norm_eq_one hk hp) hwp⟩

/-- Dirichlet layer approximants for a trace-zero slit piece belong to
`SingleCc k b₁ false` for every index and either arc-1 flag, with convergence
of their values and directional derivatives. -/
theorem dirichlet_layer_singleCc {k : ℕ} (hk : 1 ≤ k) (b₁ : Bool)
    (u : ComplexH1) (hm : arcTrace (boundaryArc k 0) u = 0) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆
      (seamDomain (boundaryArc k 0) (isOpen_boundaryArc k 0) : Set ℂ)) :
    let v := fun z => χ z • joinedDiskValue u 0 0 z
    let W := fun z => χ z • joinedDiskJet u 0 0 z +
      (fderiv ℝ χ z).smulRight (joinedDiskValue u 0 0 z)
    ∃ f : ℕ → ℂ → ℂ,
      (∀ n, f n ∈ SingleCc k b₁ false) ∧
      Tendsto (fun n => eLpNorm (fun z => f n z - v z) 2 volume)
        atTop (𝓝 0) ∧
      ∀ d, Tendsto (fun n =>
          eLpNorm (fun z => fderiv ℝ (f n) z d - W z d) 2 volume)
        atTop (𝓝 0) := by
  dsimp only
  obtain ⟨_, _, f, _, _, hsm, hvan, hext, _, hval, hjet⟩ :=
    dirichlet_layer_approximation (isOpen_boundaryArc k 0) u hm hχ hc hs
  refine ⟨f, fun n => ?_, hval, hjet⟩
  obtain ⟨δ, hδ, hv⟩ := hvan n
  exact singleCc_of_dirichlet_clauses hk b₁ (hsm n) hδ hv (hext n)

end KsIndex.Trace
