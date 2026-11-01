module

public import KsIndexLean.WeakH1Adapter
public import KsIndexLean.AristotleCollarConvergence
public import KsIndexLean.PolarPullback
public import KsIndexLean.ReflectedWeakLocalization
public import KsIndexLean.SeamMollificationSupport
public import KsIndexLean.BoundaryMollifierCore
public import KsIndexLean.CompactWeakMollification
public import KsIndexLean.LocalizedReflectedApproximation
public import KsIndexLean.DirichletLayerApproximation
public import KsIndexLean.PuncturedBoundaryPartition
public import KsIndexLean.FiniteWeakPartition
public import KsIndexLean.A1PunctureWiring
public import KsIndexLean.WeakBoundaryDomains

@[expose] public section


/-!
# Collar and disk H¹ convergence

`complexH1_tendsto_of_components` lifts convergence of the value and two
first-derivative coordinates in disk `L²` to convergence in `ComplexH1`,
using its exact graph-norm identity. Collar-supported estimates and whole-plane
mollification estimates supply these component limits for boundary and
interior pieces.

The final theorem `sIII_boundary_assembly` combines finitely many pieces for
a mixed-trace-domain field that vanishes near the punctures. It retains this
puncture-hole hypothesis and supplies smooth approximants with the appropriate
Neumann reflection or Dirichlet vanishing conditions. Removing the hole
hypothesis to obtain a density theorem is a separate step.
-/

open Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- `dxLp` is additive on differences (it is the underlying map of the CLM `dxCLM`). -/
lemma dxLp_sub (a b : ComplexH1) : dxLp (a - b) = dxLp a - dxLp b :=
  map_sub dxCLM a b

/-- `dyLp` is additive on differences (underlying map of `dyCLM`). -/
lemma dyLp_sub (a b : ComplexH1) : dyLp (a - b) = dyLp a - dyLp b :=
  map_sub dyCLM a b

lemma dxLp_add (a b : ComplexH1) : dxLp (a + b) = dxLp a + dxLp b :=
  map_add dxCLM a b
lemma dyLp_add (a b : ComplexH1) : dyLp (a + b) = dyLp a + dyLp b :=
  map_add dyCLM a b
lemma dxLp_sum {ι : Type*} (s : Finset ι) (f : ι → ComplexH1) :
    dxLp (∑ i ∈ s, f i) = ∑ i ∈ s, dxLp (f i) := map_sum dxCLM f s
lemma dyLp_sum {ι : Type*} (s : Finset ι) (f : ι → ComplexH1) :
    dyLp (∑ i ∈ s, f i) = ∑ i ∈ s, dyLp (f i) := map_sum dyCLM f s

/-- Convergence of the value and both first-derivative coordinates in disk
`L²` implies convergence in `ComplexH1`. The three component convergences
are separate hypotheses; the proof uses the exact graph-norm identity. -/
theorem complexH1_tendsto_of_components {un : ℕ → ComplexH1} {u : ComplexH1}
    (hv : Tendsto (fun n => valueCLM (un n)) atTop (𝓝 (valueCLM u)))
    (hx : Tendsto (fun n => dxLp (un n)) atTop (𝓝 (dxLp u)))
    (hy : Tendsto (fun n => dyLp (un n)) atTop (𝓝 (dyLp u))) :
    Tendsto un atTop (𝓝 u) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  -- each coordinate difference tends to 0 in L²(disk), hence its squared norm → 0
  have ha : Tendsto (fun n => ‖valueCLM (un n) - valueCLM u‖ ^ 2) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n => valueCLM (un n) - valueCLM u) atTop (𝓝 0) := by
      simpa using hv.sub_const (valueCLM u)
    simpa using (h0.norm.pow 2)
  have hb : Tendsto (fun n => ‖dxLp (un n) - dxLp u‖ ^ 2) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n => dxLp (un n) - dxLp u) atTop (𝓝 0) := by
      simpa using hx.sub_const (dxLp u)
    simpa using (h0.norm.pow 2)
  have hc : Tendsto (fun n => ‖dyLp (un n) - dyLp u‖ ^ 2) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n => dyLp (un n) - dyLp u) atTop (𝓝 0) := by
      simpa using hy.sub_const (dyLp u)
    simpa using (h0.norm.pow 2)
  have hsum : Tendsto (fun n => ‖valueCLM (un n) - valueCLM u‖ ^ 2
      + ‖dxLp (un n) - dxLp u‖ ^ 2 + ‖dyLp (un n) - dyLp u‖ ^ 2) atTop (𝓝 0) := by
    simpa using (ha.add hb).add hc
  -- the coordinate graph norm identifies that sum with ‖uₙ − u‖²
  have hsq : Tendsto (fun n => ‖un n - u‖ ^ 2) atTop (𝓝 0) :=
    hsum.congr fun n =>
      (jet_graph_norm_sq (map_sub valueCLM (un n) u)
        (dxLp_sub (un n) u) (dyLp_sub (un n) u)).symm
  -- ‖·‖² → 0  ⟹  ‖·‖ → 0
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt

/-! ### Disk integrability of collar-supported functions -/

/-- A function that is `L²` on the collar `annulusSet (1/2) 2` and vanishes on
`{‖z‖ ≤ 1/2}` is `L²` on the unit disk: the only part of the disk outside the
collar is `{‖z‖ ≤ 1/2}`, where the function is zero (the disk⊄collar complement).
Uses the ported `eLpNorm_restrict_le_of_ae_eq_zero_on_diff`. -/
lemma memLp_disk_of_collar_supported {f : ℂ → ℂ}
    (hmeas : AEStronglyMeasurable f volume)
    (hcol : MemLp f 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
    (hz : ∀ z, ‖z‖ ≤ 1 / 2 → f z = 0) :
    MemLp f 2 (volume.restrict (Metric.ball (0 : ℂ) 1)) := by
  have hA : MeasurableSet (annulusSet (1 / 2 : ℝ) 2) :=
    (annulusOpens (1 / 2 : ℝ) 2).isOpen.measurableSet
  have h0 : ∀ᵐ z ∂volume.restrict
      (Metric.ball (0 : ℂ) 1 \ annulusSet (1 / 2 : ℝ) 2), f z = 0 := by
    filter_upwards [ae_restrict_mem
      (measurableSet_ball.diff hA)] with z hz'
    -- off the collar but inside the disk ⟹ ‖z‖ ≤ 1/2
    have h1 : ‖z‖ < 1 := by simpa [Complex.dist_eq] using hz'.1
    have hnotA : z ∉ annulusSet (1 / 2 : ℝ) 2 := hz'.2
    apply hz
    by_contra hlt
    exact hnotA (mem_annulusSet.mpr ⟨lt_of_not_ge hlt, h1.trans (by norm_num)⟩)
  exact lt_of_le_of_lt
    (AstraAristotle.eLpNorm_restrict_le_of_ae_eq_zero_on_diff hA (by simp) (by simp) h0) hcol.eLpNorm_lt_top

/-- **Collar-to-disk L² convergence.** An `L²(collar)`-convergent sequence whose
members are eventually supported in the collar `annulusSet (1/2) 2`, with limit
`g` vanishing on `{‖z‖ ≤ 1/2}`, converges in `L²(disk)`. A re-exposure of the
ported `collar_supported_disk_tendsto` in the project's `annulusSet` vocabulary
(the collar set is defeq to the ported lemma's literal `{z | 1/2 < ‖z‖ < 2}`). -/
theorem collar_to_disk_tendsto {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hfA : ∀ n, MemLp (f n) 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
    (hgA : MemLp g 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
    (hfD : ∀ n, MemLp (f n) 2 (volume.restrict (Metric.ball (0 : ℂ) 1)))
    (hgD : MemLp g 2 (volume.restrict (Metric.ball (0 : ℂ) 1)))
    (hs : ∀ᶠ n in atTop, tsupport (f n) ⊆ annulusSet (1 / 2 : ℝ) 2)
    (hg : ∀ z, ‖z‖ ≤ 1 / 2 → g z = 0)
    (ht : Tendsto (fun n => (hfA n).toLp (f n)) atTop (𝓝 (hgA.toLp g))) :
    Tendsto (fun n => (hfD n).toLp (f n)) atTop (𝓝 (hgD.toLp g)) :=
  AstraAristotle.collar_supported_disk_tendsto hfA hgA hfD hgD hs (ae_of_all _ hg) ht

/-! ### Weak jets and smooth functions as H¹ carriers -/

/-- **Smooth→carrier packaging.** A function `v` with a disk weak derivative `J`
(and the value + directional-derivative `L²(disk)` bounds) has a `ComplexH1`
carrier whose three coordinates recover `v`, `J·1`, and `J·i` a.e. The single
carrier construction applies to the limit piece (via
`reflected_weak_localization`, after `.mono le_top`) and for each smooth
approximant. Built on `exists_unique_carrier_of_jet`; `realLinear_coordinates`
turns the abstract jet `J` into the `Dxy` coordinate form. -/
theorem carrier_of_weakJet {v : ℂ → ℂ} {J : ℂ → ℂ →L[ℝ] ℂ}
    (hJ : TauCeti.HasWeakFDerivOn volume disk v J)
    (hv : MemLp v 2 (volume.restrict (disk : Set ℂ)))
    (hd : ∀ d, MemLp (fun z => J z d) 2 (volume.restrict (disk : Set ℂ))) :
    ∃ u : ComplexH1,
      (valueCLM u : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] v ∧
      (dxLp u : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] (fun z => J z 1) ∧
      (dyLp u : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] (fun z => J z Complex.I) := by
  have hJeq : J = Dxy (fun z => J z 1) (fun z => J z Complex.I) := by
    funext z; ext w; rw [Dxy_apply]; exact realLinear_coordinates (J z) w
  have hw : HasComplexH1Jet (hv.toLp v)
      ((hd 1).toLp (fun z => J z 1)) ((hd Complex.I).toLp (fun z => J z Complex.I)) := by
    have h1 : TauCeti.HasWeakFDerivOn volume disk v
        (Dxy (fun z => J z 1) (fun z => J z Complex.I)) := hJeq ▸ hJ
    refine (h1.congr_ae hv.coeFn_toLp.symm).congr_ae_deriv ?_
    filter_upwards [(hd 1).coeFn_toLp, (hd Complex.I).coeFn_toLp] with z hx hy
    ext w
    simp only [Dxy_apply, hx, hy]
  obtain ⟨u, hu, -⟩ := exists_unique_carrier_of_jet _ _ _ hw
  refine ⟨u, ?_, ?_, ?_⟩
  · rw [hu.1]; exact hv.coeFn_toLp
  · rw [hu.2.1]; exact (hd 1).coeFn_toLp
  · rw [hu.2.2]; exact (hd Complex.I).coeFn_toLp

/-- A globally smooth, compactly supported function has a `ComplexH1` carrier
recovering its value and classical partial derivatives a.e. on the disk. This is
the approximant case of the smooth→carrier packaging: the reflected mollifiers,
once `0 ∉` their support, are `ContDiff ℝ ∞` with compact support
(`reflectionAverage_smooth_of_zero_not_support`), so their weak jet is the
classical `fderiv`. -/
theorem smooth_compactSupport_carrier {h : ℂ → ℂ}
    (hsmooth : ContDiff ℝ ∞ h) (hcomp : HasCompactSupport h) :
    ∃ u : ComplexH1,
      (valueCLM u : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] h ∧
      (dxLp u : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] (fun z => fderiv ℝ h z 1) ∧
      (dyLp u : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
        (fun z => fderiv ℝ h z Complex.I) := by
  have hcont : Continuous h := hsmooth.continuous
  have hdiff : Differentiable ℝ h := hsmooth.differentiable (by norm_num)
  have hfd : Continuous (fun z => fderiv ℝ h z) := hsmooth.continuous_fderiv (by norm_num)
  have hcompFd : HasCompactSupport (fun z => fderiv ℝ h z) := hcomp.fderiv ℝ
  have hJ : TauCeti.HasWeakFDerivOn volume disk h (fun z => fderiv ℝ h z) :=
    TauCeti.hasWeakFDerivOn_of_differentiableOn
      (hcont.locallyIntegrable.locallyIntegrableOn _)
      (hfd.locallyIntegrable.locallyIntegrableOn _) (fun x _ => hdiff x)
  have hv : MemLp h 2 (volume.restrict (disk : Set ℂ)) :=
    (hcont.memLp_of_hasCompactSupport (μ := volume) hcomp).mono_measure Measure.restrict_le_self
  have hd : ∀ d, MemLp (fun z => fderiv ℝ h z d) 2 (volume.restrict (disk : Set ℂ)) := by
    intro d
    have hcd : Continuous (fun z => fderiv ℝ h z d) :=
      (ContinuousLinearMap.apply ℝ ℂ d).continuous.comp hfd
    have hccd : HasCompactSupport (fun z => fderiv ℝ h z d) :=
      hcompFd.comp_left (g := fun L : ℂ →L[ℝ] ℂ => L d) (by simp)
    exact (hcd.memLp_of_hasCompactSupport (μ := volume) hccd).mono_measure Measure.restrict_le_self
  exact carrier_of_weakJet hJ hv hd

/-- **The limit-piece carrier.** The boundary piece `v = χ • joinedDiskValue u u s`
(the a.e.-limit of the reflected approximants) has a `ComplexH1` carrier
recovering its value and weak-jet coordinates a.e. on the disk. Its jet is
supplied by `reflected_weak_localization` (on `⊤`), restricted to the
disk. -/
theorem piece_limit_carrier {A : Set Circle₁} (hA : IsOpen A)
    (u : ComplexH1) (s : ℂ) (hsign : s ^ 2 = 1)
    (hm : arcTrace A u = s • arcTrace A u) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hsupp : tsupport χ ⊆ (seamDomain A hA : Set ℂ))
    (hi : ∀ z, χ (KsIndex.Bracket.σ z) = χ z) :
    ∃ w : ComplexH1,
      (valueCLM w : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
        (fun z => χ z • joinedDiskValue u u s z) ∧
      (dxLp w : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
        (fun z => (χ z • joinedDiskJet u u s z
          + (fderiv ℝ χ z).smulRight (joinedDiskValue u u s z)) 1) ∧
      (dyLp w : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
        (fun z => (χ z • joinedDiskJet u u s z
          + (fderiv ℝ χ z).smulRight (joinedDiskValue u u s z)) Complex.I) := by
  obtain ⟨hw, hv, hJd, -, -⟩ := reflected_weak_localization hA u s hsign hm hχ hc hsupp hi
  exact carrier_of_weakJet (hw.mono le_top) (hv.mono_measure Measure.restrict_le_self)
    (fun d => (hJd d).mono_measure Measure.restrict_le_self)

/-- **Eventual approximant carriers.** Eventually in `n`, the
reflected mollifier of the boundary piece `v = χ • joinedDiskValue u u s` has a
`ComplexH1` carrier recovering its value and classical partials a.e. on the disk.
Once `0 ∉` the mollifier's support (`reflected_mollifier_support_seam` +
`zero_notMem_seamDomain`), it is globally `ContDiff ℝ ∞` with compact support, so
`smooth_compactSupport_carrier` applies. -/
theorem eventually_approx_carrier {A : Set Circle₁} (hA : IsOpen A)
    (u : ComplexH1) (s : ℂ) (hsign : s ^ 2 = 1)
    (hm : arcTrace A u = s • arcTrace A u) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hsupp : tsupport χ ⊆ (seamDomain A hA : Set ℂ))
    (hi : ∀ z, χ (KsIndex.Bracket.σ z) = χ z) :
    ∀ᶠ n in atTop, ∃ w : ComplexH1,
      (valueCLM w : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
        reflectionAverage s (compactMollify (shrinkingMollifier n)
          (fun z => χ z • joinedDiskValue u u s z)) ∧
      (dxLp w : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
        (fun z => fderiv ℝ (reflectionAverage s (compactMollify (shrinkingMollifier n)
          (fun z => χ z • joinedDiskValue u u s z))) z 1) ∧
      (dyLp w : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
        (fun z => fderiv ℝ (reflectionAverage s (compactMollify (shrinkingMollifier n)
          (fun z => χ z • joinedDiskValue u u s z))) z Complex.I) := by
  obtain ⟨_, hvmem, _, _, _⟩ := reflected_weak_localization hA u s hsign hm hχ hc hsupp hi
  have hcv : HasCompactSupport (fun z => χ z • joinedDiskValue u u s z) := hc.smul_right
  have hsv : tsupport (fun z => χ z • joinedDiskValue u u s z) ⊆ (seamDomain A hA : Set ℂ) :=
    (tsupport_smul_subset_left χ _).trans hsupp
  filter_upwards [reflected_mollifier_support_seam s hA hcv hsv] with n hn
  have h0 : (0 : ℂ) ∉ tsupport (reflectionAverage s
      (compactMollify (shrinkingMollifier n) (fun z => χ z • joinedDiskValue u u s z))) :=
    fun h => zero_notMem_seamDomain hA (hn h)
  have hsmooth : ContDiff ℝ ∞ (reflectionAverage s
      (compactMollify (shrinkingMollifier n) (fun z => χ z • joinedDiskValue u u s z))) :=
    reflectionAverage_smooth_of_zero_not_support s
      (compactMollify_smooth (shrinkingMollifier n) hvmem) h0
  have hcomp : HasCompactSupport (reflectionAverage s
      (compactMollify (shrinkingMollifier n) (fun z => χ z • joinedDiskValue u u s z))) :=
    (isCompact_closedBall (0 : ℂ) 2).of_isClosed_subset (isClosed_tsupport _)
      (hn.trans fun z hz => by
        rw [Metric.mem_closedBall, dist_zero_right]; exact (mem_annulusSet.mp hz.1).2.le)
  exact smooth_compactSupport_carrier hsmooth hcomp

/-- **From eventual carriers to a convergent sequence.** Given a
family of `L²(disk)` component sequences `fv, fx, fy` that converge to a carrier
`u_v`'s three coordinates, and that eventually are the coordinates of some
`ComplexH1` element, there is a total sequence `U` converging to `u_v` whose
coordinates eventually match `fv, fx, fy`. This isolates the eventual-smoothness
bookkeeping (choice + `Tendsto.congr'`) from the collar plumbing; `U`'s
convergence follows from the graph-norm identity and component convergence. -/
theorem tendsto_of_eventual_component_carrier {u_v : ComplexH1} {fv fx fy : ℕ → L2C}
    (hc : ∀ᶠ n in atTop, ∃ w : ComplexH1,
      valueCLM w = fv n ∧ dxLp w = fx n ∧ dyLp w = fy n)
    (hv : Tendsto fv atTop (𝓝 (valueCLM u_v)))
    (hx : Tendsto fx atTop (𝓝 (dxLp u_v)))
    (hy : Tendsto fy atTop (𝓝 (dyLp u_v))) :
    ∃ U : ℕ → ComplexH1, Tendsto U atTop (𝓝 u_v) ∧
      ∀ᶠ n in atTop, valueCLM (U n) = fv n ∧ dxLp (U n) = fx n ∧ dyLp (U n) = fy n := by
  classical
  rw [eventually_atTop] at hc
  obtain ⟨N, hN⟩ := hc
  refine ⟨fun n => if h : N ≤ n then Classical.choose (hN n h) else 0, ?_, ?_⟩
  · refine complexH1_tendsto_of_components (hv.congr' ?_) (hx.congr' ?_) (hy.congr' ?_)
    · filter_upwards [eventually_ge_atTop N] with n hn
      simp only [dif_pos hn]; exact ((Classical.choose_spec (hN n hn)).1).symm
    · filter_upwards [eventually_ge_atTop N] with n hn
      simp only [dif_pos hn]; exact ((Classical.choose_spec (hN n hn)).2.1).symm
    · filter_upwards [eventually_ge_atTop N] with n hn
      simp only [dif_pos hn]; exact ((Classical.choose_spec (hN n hn)).2.2).symm
  · filter_upwards [eventually_ge_atTop N] with n hn
    simp only [dif_pos hn]; exact Classical.choose_spec (hN n hn)

/-! ### Convergence of individual pieces -/

/-- **Collar component estimate.** If the `L²(disk)` elements `a n` and `b` are a.e.
the functions `hf n` and `g`, both vanishing on `{‖z‖ ≤ 1/2}` (eventually for
`hf n`), and the collar `L²`-norm of `hf n − g` tends to `0`, then `a n → b` in
`L²(disk)`. The difference `hf n − g` vanishes off the collar, so its disk norm
is bounded by its collar norm (the disk⊄collar estimate applied to the
difference) — no `∀n` disk-integrability needed. -/
lemma component_tendsto_of_collar {a : ℕ → L2C} {b : L2C} {hf : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (ha : ∀ᶠ n in atTop, (↑(a n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] hf n)
    (hb : (↑b : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] g)
    (hfz : ∀ᶠ n in atTop, ∀ z, ‖z‖ ≤ 1 / 2 → hf n z = 0)
    (hgz : ∀ z, ‖z‖ ≤ 1 / 2 → g z = 0)
    (hfin : ∀ᶠ n in atTop, eLpNorm (fun z => hf n z - g z) 2
      (volume.restrict (annulusSet (1 / 2 : ℝ) 2)) ≠ ⊤)
    (hcollar : Tendsto (fun n => (eLpNorm (fun z => hf n z - g z) 2
      (volume.restrict (annulusSet (1 / 2 : ℝ) 2))).toReal) atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 b) := by
  have hA : MeasurableSet (annulusSet (1 / 2 : ℝ) 2) :=
    (annulusOpens (1 / 2 : ℝ) 2).isOpen.measurableSet
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hcollar
  filter_upwards [ha, hfz, hfin] with n han hfzn hfinn
  have hdiff : (↑(a n - b) : ℂ → ℂ)
      =ᵐ[volume.restrict (disk : Set ℂ)] (fun z => hf n z - g z) := by
    filter_upwards [Lp.coeFn_sub (a n) b, han, hb] with z hz h1 h2
    rw [hz, Pi.sub_apply, h1, h2]
  have hzero : ∀ᵐ z ∂volume.restrict
      (Metric.ball (0 : ℂ) 1 \ annulusSet (1 / 2 : ℝ) 2), (fun z => hf n z - g z) z = 0 := by
    filter_upwards [ae_restrict_mem (measurableSet_ball.diff hA)] with z hz'
    have h1 : ‖z‖ < 1 := by simpa [Complex.dist_eq] using hz'.1
    have hnotA : z ∉ annulusSet (1 / 2 : ℝ) 2 := hz'.2
    have hle : ‖z‖ ≤ 1 / 2 := by
      by_contra hlt
      exact hnotA (mem_annulusSet.mpr ⟨lt_of_not_ge hlt, h1.trans (by norm_num)⟩)
    simp [hfzn z hle, hgz z hle]
  rw [Lp.norm_def, eLpNorm_congr_ae hdiff]
  exact ENNReal.toReal_mono hfinn
    (AstraAristotle.eLpNorm_restrict_le_of_ae_eq_zero_on_diff hA (by simp) (by simp) hzero)

/-- **Whole-plane component estimate.** If the `L²(disk)` elements `a n`, `b`
are a.e. `hf n`, `g`, and the whole-plane `L²`-norm of `hf n − g` tends to `0`,
then `a n → b` in `L²(disk)`: the disk norm is `≤` the whole-plane norm
(`eLpNorm_mono_measure`). For the interior and Dirichlet pieces, whose suppliers
give whole-plane convergence directly — no collar detour, no vanishing needed. -/
lemma component_tendsto_of_wholeplane {a : ℕ → L2C} {b : L2C} {hf : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (ha : ∀ᶠ n in atTop, (↑(a n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] hf n)
    (hb : (↑b : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] g)
    (hfin : ∀ᶠ n in atTop, eLpNorm (fun z => hf n z - g z) 2 volume ≠ ⊤)
    (hconv : Tendsto (fun n => (eLpNorm (fun z => hf n z - g z) 2 volume).toReal)
      atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 b) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hconv
  filter_upwards [ha, hfin] with n han hfinn
  have hdiff : (↑(a n - b) : ℂ → ℂ)
      =ᵐ[volume.restrict (disk : Set ℂ)] (fun z => hf n z - g z) := by
    filter_upwards [Lp.coeFn_sub (a n) b, han, hb] with z hz h1 h2
    rw [hz, Pi.sub_apply, h1, h2]
  rw [Lp.norm_def, eLpNorm_congr_ae hdiff]
  exact ENNReal.toReal_mono hfinn (eLpNorm_mono_measure _ Measure.restrict_le_self)

/-- From a collar `L²`-convergent sequence `fc → gc` whose members and limit are
a.e. the functions `hf n` and `g`, the collar `eLpNorm` of `hf n − g` is finite
and its real value tends to `0` — the two collar hypotheses `component_tendsto_of_collar`
needs, packaged from the supplier's `Lp`-collar convergence. -/
lemma collar_diff_tendsto
    {fc : ℕ → Lp ℂ 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2))}
    {gc : Lp ℂ 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2))}
    {hf : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hfc : ∀ n, (↑(fc n) : ℂ → ℂ) =ᵐ[volume.restrict (annulusSet (1 / 2 : ℝ) 2)] hf n)
    (hgc : (↑gc : ℂ → ℂ) =ᵐ[volume.restrict (annulusSet (1 / 2 : ℝ) 2)] g)
    (ht : Tendsto fc atTop (𝓝 gc)) :
    (∀ n, eLpNorm (fun z => hf n z - g z) 2
        (volume.restrict (annulusSet (1 / 2 : ℝ) 2)) ≠ ⊤) ∧
    Tendsto (fun n => (eLpNorm (fun z => hf n z - g z) 2
        (volume.restrict (annulusSet (1 / 2 : ℝ) 2))).toReal) atTop (𝓝 0) := by
  have hae : ∀ n, (fun z => hf n z - g z)
      =ᵐ[volume.restrict (annulusSet (1 / 2 : ℝ) 2)] (↑(fc n - gc) : ℂ → ℂ) := by
    intro n
    filter_upwards [Lp.coeFn_sub (fc n) gc, hfc n, hgc] with z hz h1 h2
    rw [hz, Pi.sub_apply, h1, h2]
  have heq : ∀ n, eLpNorm (fun z => hf n z - g z) 2
      (volume.restrict (annulusSet (1 / 2 : ℝ) 2)) = eLpNorm (↑(fc n - gc)) 2
      (volume.restrict (annulusSet (1 / 2 : ℝ) 2)) := fun n => eLpNorm_congr_ae (hae n)
  refine ⟨fun n => by rw [heq n]; exact (Lp.memLp (fc n - gc)).eLpNorm_lt_top.ne, ?_⟩
  have hnorm : Tendsto (fun n => ‖fc n - gc‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp ht
  refine hnorm.congr fun n => ?_
  rw [Lp.norm_def, ← heq n]

/-- Measure-general form of `collar_diff_tendsto`: from `Lp μ`-convergence
`fc → gc` with `fc n`, `gc` a.e. `hf n`, `g`, the `μ`-`eLpNorm` of `hf n − g` is
finite and `→ 0` in real value. Used for the interior/Dirichlet pieces at
`μ = volume` (their suppliers converge on the whole plane). -/
lemma diff_tendsto_of_toLp {μ : Measure ℂ} {fc : ℕ → Lp ℂ 2 μ} {gc : Lp ℂ 2 μ}
    {hf : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hfc : ∀ n, (↑(fc n) : ℂ → ℂ) =ᵐ[μ] hf n)
    (hgc : (↑gc : ℂ → ℂ) =ᵐ[μ] g)
    (ht : Tendsto fc atTop (𝓝 gc)) :
    (∀ n, eLpNorm (fun z => hf n z - g z) 2 μ ≠ ⊤) ∧
    Tendsto (fun n => (eLpNorm (fun z => hf n z - g z) 2 μ).toReal) atTop (𝓝 0) := by
  have hae : ∀ n, (fun z => hf n z - g z) =ᵐ[μ] (↑(fc n - gc) : ℂ → ℂ) := by
    intro n
    filter_upwards [Lp.coeFn_sub (fc n) gc, hfc n, hgc] with z hz h1 h2
    rw [hz, Pi.sub_apply, h1, h2]
  have heq : ∀ n, eLpNorm (fun z => hf n z - g z) 2 μ = eLpNorm (↑(fc n - gc)) 2 μ :=
    fun n => eLpNorm_congr_ae (hae n)
  refine ⟨fun n => by rw [heq n]; exact (Lp.memLp (fc n - gc)).eLpNorm_lt_top.ne, ?_⟩
  have hnorm : Tendsto (fun n => ‖fc n - gc‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp ht
  refine hnorm.congr fun n => ?_
  rw [Lp.norm_def, ← heq n]

/-- Off its support, the classical derivative of `f` vanishes (as a map). -/
lemma fderiv_apply_eq_zero_of_notMem_tsupport {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℂ → F} {z : ℂ}
    (h : z ∉ tsupport f) (w : ℂ) : fderiv ℝ f z w = 0 := by
  have he : f =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp h
  rw [he.fderiv_eq]
  simp

/-- **Per-piece `ComplexH1` convergence with coordinate identities.** For a boundary
piece `(A, u, s, χ)`, the reflected-mollifier carriers converge in `ComplexH1`
to the piece's limit carrier `u_v`, and the family is given with its value and
both directional-derivative coordinate identifications almost everywhere on the disk. -/
theorem piece_carrier_tendsto {A : Set Circle₁} (hA : IsOpen A)
    (u : ComplexH1) (s : ℂ) (hsign : s ^ 2 = 1)
    (hm : arcTrace A u = s • arcTrace A u) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hsupp : tsupport χ ⊆ (seamDomain A hA : Set ℂ))
    (hi : ∀ z, χ (KsIndex.Bracket.σ z) = χ z) :
    ∃ (u_v : ComplexH1) (U : ℕ → ComplexH1),
      Tendsto U atTop (𝓝 u_v) ∧
      ((valueCLM u_v : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
        (fun z => χ z • joinedDiskValue u u s z)) ∧
      ∀ᶠ n in atTop,
        ((valueCLM (U n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
          reflectionAverage s (compactMollify (shrinkingMollifier n)
            (fun z => χ z • joinedDiskValue u u s z))) ∧
        ((dxLp (U n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
          (fun z => fderiv ℝ (reflectionAverage s (compactMollify (shrinkingMollifier n)
            (fun z => χ z • joinedDiskValue u u s z))) z 1)) ∧
        ((dyLp (U n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
          (fun z => fderiv ℝ (reflectionAverage s (compactMollify (shrinkingMollifier n)
            (fun z => χ z • joinedDiskValue u u s z))) z Complex.I)) := by
  classical
  obtain ⟨u_v, hval_v, hdx_v, hdy_v⟩ := piece_limit_carrier hA u s hsign hm hχ hc hsupp hi
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_approx_carrier hA u s hsign hm hχ hc hsupp hi)
  obtain ⟨hv, hW, fv, fD, _hCD, hfv, hfD, htv, htD⟩ :=
    localized_reflected_approximation hA u s hsign hm hχ hc hsupp hi
  have hcv : HasCompactSupport (fun z => χ z • joinedDiskValue u u s z) := hc.smul_right
  have hsv : tsupport (fun z => χ z • joinedDiskValue u u s z) ⊆ (seamDomain A hA : Set ℂ) :=
    (tsupport_smul_subset_left χ _).trans hsupp
  have hseam := reflected_mollifier_support_seam s hA hcv hsv
  -- points with ‖z‖ ≤ 1/2 are outside the seam domain
  have hnotseam : ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → z ∉ (seamDomain A hA : Set ℂ) :=
    fun z hz hmem => absurd (mem_annulusSet.mp hmem.1).1 (not_lt.mpr hz)
  have hχz : ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → χ z = 0 :=
    fun z hz => image_eq_zero_of_notMem_tsupport (fun h => hnotseam z hz (hsupp h))
  have hχfd : ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → ∀ w, fderiv ℝ χ z w = 0 :=
    fun z hz w => fderiv_apply_eq_zero_of_notMem_tsupport (f := χ)
      (fun h => hnotseam z hz (hsupp h)) w
  set U : ℕ → ComplexH1 := fun n => if h : N ≤ n then Classical.choose (hN n h) else 0 with hUdef
  have hUspec : ∀ᶠ n in atTop,
      ((valueCLM (U n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
        reflectionAverage s (compactMollify (shrinkingMollifier n)
          (fun z => χ z • joinedDiskValue u u s z))) ∧
      ((dxLp (U n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
        (fun z => fderiv ℝ (reflectionAverage s (compactMollify (shrinkingMollifier n)
          (fun z => χ z • joinedDiskValue u u s z))) z 1)) ∧
      ((dyLp (U n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
        (fun z => fderiv ℝ (reflectionAverage s (compactMollify (shrinkingMollifier n)
          (fun z => χ z • joinedDiskValue u u s z))) z Complex.I)) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    simp only [hUdef, dif_pos hn]; exact Classical.choose_spec (hN n hn)
  refine ⟨u_v, U, ?_, hval_v, hUspec⟩
  -- convergence of each component through the collar estimate
  refine complexH1_tendsto_of_components ?_ ?_ ?_
  · -- value
    have hcd := collar_diff_tendsto hfv
      (hv.mono_measure Measure.restrict_le_self).coeFn_toLp htv
    refine component_tendsto_of_collar
      (g := fun z => χ z • joinedDiskValue u u s z)
      (hUspec.mono fun n h => h.1) hval_v ?_ ?_ (Eventually.of_forall hcd.1) hcd.2
    · filter_upwards [hseam] with n hn z hz
      exact image_eq_zero_of_notMem_tsupport (fun h => hnotseam z hz (hn h))
    · intro z hz; simp [hχz z hz]
  · -- dx
    have hcd := collar_diff_tendsto (fun n => hfD n 1)
      ((hW 1).mono_measure Measure.restrict_le_self).coeFn_toLp (htD 1)
    refine component_tendsto_of_collar
      (g := fun z => (χ z • joinedDiskJet u u s z
        + (fderiv ℝ χ z).smulRight (joinedDiskValue u u s z)) 1)
      (hUspec.mono fun n h => h.2.1) hdx_v ?_ ?_ (Eventually.of_forall hcd.1) hcd.2
    · filter_upwards [hseam] with n hn z hz
      exact fderiv_apply_eq_zero_of_notMem_tsupport (fun h => hnotseam z hz (hn h)) 1
    · intro z hz
      simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
        hχz z hz, hχfd z hz 1]
  · -- dy
    have hcd := collar_diff_tendsto (fun n => hfD n Complex.I)
      ((hW Complex.I).mono_measure Measure.restrict_le_self).coeFn_toLp (htD Complex.I)
    refine component_tendsto_of_collar
      (g := fun z => (χ z • joinedDiskJet u u s z
        + (fderiv ℝ χ z).smulRight (joinedDiskValue u u s z)) Complex.I)
      (hUspec.mono fun n h => h.2.2) hdy_v ?_ ?_ (Eventually.of_forall hcd.1) hcd.2
    · filter_upwards [hseam] with n hn z hz
      exact fderiv_apply_eq_zero_of_notMem_tsupport (fun h => hnotseam z hz (hn h)) Complex.I
    · intro z hz
      simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
        hχz z hz, hχfd z hz Complex.I]

/-- **Interior-piece convergence.** For a smooth compactly-supported cutoff
`χ` on `Ω` and a weak-`H¹` function `u` (jet `U`), the mollified interior pieces
`compactMollify (shrinkingMollifier n) (χ•u)` have `ComplexH1` carriers
converging to `χ•u`'s carrier, with the value + directional-derivative
coordinate identifications exposed. Whole-plane convergence
(`localized_mollification`), so no collar detour; all-`n` smooth. -/
theorem interior_piece_carrier_tendsto {Ω : TopologicalSpace.Opens ℂ} {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ (Ω : Set ℂ))
    {u : ℂ → ℂ} {U : ℂ → ℂ →L[ℝ] ℂ} (hw : TauCeti.HasWeakFDerivOn volume Ω u U)
    (hu : MemLp u 2 (volume.restrict (Ω : Set ℂ)))
    (hU : ∀ d, MemLp (fun z => U z d) 2 (volume.restrict (Ω : Set ℂ))) :
    ∃ (u_v : ComplexH1) (g₀ : ℕ → ℂ → ℂ) (U_seq : ℕ → ComplexH1),
      (∀ n, g₀ n = compactMollify (shrinkingMollifier n) (fun z => χ z • u z)) ∧
      (∀ n, ContDiff ℝ ∞ (g₀ n) ∧ HasCompactSupport (g₀ n)) ∧
      Tendsto U_seq atTop (𝓝 u_v) ∧
      ((valueCLM u_v : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] (fun z => χ z • u z)) ∧
      ∀ n,
        ((valueCLM (U_seq n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] g₀ n) ∧
        ((dxLp (U_seq n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
          (fun z => fderiv ℝ (g₀ n) z 1)) ∧
        ((dyLp (U_seq n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
          (fun z => fderiv ℝ (g₀ n) z Complex.I)) := by
  classical
  obtain ⟨hjet, hv, hV⟩ := weakH1_localization hχ hc hs hw hu hU
  obtain ⟨u_v, hval_v, hdx_v, hdy_v⟩ :=
    carrier_of_weakJet (hjet.mono le_top) (hv.mono_measure Measure.restrict_le_self)
      (fun d => (hV d).mono_measure Measure.restrict_le_self)
  obtain ⟨hv', hV', fv, fV, hsm, hfv, hfV, htv, htV⟩ :=
    localized_mollification hχ hc hs hw hu hU shrinkingMollifier_radius
  -- the mollified interior pieces are smooth with compact support
  have hg₀c : ∀ n, HasCompactSupport (compactMollify (shrinkingMollifier n)
      (fun z => χ z • u z)) := fun n => compactMollify_support _ hc.smul_right
  -- carriers for each n
  have hcarr : ∀ n, ∃ w : ComplexH1,
      (valueCLM w : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
        compactMollify (shrinkingMollifier n) (fun z => χ z • u z) ∧
      (dxLp w : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
        (fun z => fderiv ℝ (compactMollify (shrinkingMollifier n) (fun z => χ z • u z)) z 1) ∧
      (dyLp w : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
        (fun z => fderiv ℝ (compactMollify (shrinkingMollifier n)
          (fun z => χ z • u z)) z Complex.I) :=
    fun n => smooth_compactSupport_carrier (hsm n) (hg₀c n)
  refine ⟨u_v, fun n => compactMollify (shrinkingMollifier n) (fun z => χ z • u z),
    fun n => Classical.choose (hcarr n), fun _ => rfl,
    fun n => ⟨hsm n, hg₀c n⟩, ?_, hval_v, fun n => Classical.choose_spec (hcarr n)⟩
  -- component convergence from the whole-plane estimate
  -- for smooth pieces the supplier's `lineDeriv` is the classical `fderiv`
  have hfvfd : ∀ (d : ℂ) (n : ℕ), (↑(fV n d) : ℂ → ℂ) =ᵐ[volume]
      (fun z => fderiv ℝ (compactMollify (shrinkingMollifier n) (fun z => χ z • u z)) z d) := by
    intro d n
    filter_upwards [hfV n d] with z hz
    rw [hz]
    exact (((hsm n).differentiable (by norm_num)).differentiableAt.hasFDerivAt.hasLineDerivAt
      d).lineDeriv
  refine complexH1_tendsto_of_components ?_ ?_ ?_
  · exact component_tendsto_of_wholeplane
      (Eventually.of_forall fun n => (Classical.choose_spec (hcarr n)).1) hval_v
      (Eventually.of_forall (diff_tendsto_of_toLp hfv hv'.coeFn_toLp htv).1)
      (diff_tendsto_of_toLp hfv hv'.coeFn_toLp htv).2
  · exact component_tendsto_of_wholeplane
      (Eventually.of_forall fun n => (Classical.choose_spec (hcarr n)).2.1) hdx_v
      (Eventually.of_forall (diff_tendsto_of_toLp (hfvfd 1) (hV' 1).coeFn_toLp (htV 1)).1)
      (diff_tendsto_of_toLp (hfvfd 1) (hV' 1).coeFn_toLp (htV 1)).2
  · exact component_tendsto_of_wholeplane
      (Eventually.of_forall fun n => (Classical.choose_spec (hcarr n)).2.2) hdy_v
      (Eventually.of_forall
        (diff_tendsto_of_toLp (hfvfd Complex.I) (hV' Complex.I).coeFn_toLp (htV Complex.I)).1)
      (diff_tendsto_of_toLp (hfvfd Complex.I) (hV' Complex.I).coeFn_toLp (htV Complex.I)).2

/-- **Dirichlet-piece convergence.** For a Dirichlet boundary piece
(`arcTrace A u = 0`), the `dirichlet_layer_approximation` approximants have
`ComplexH1` carriers converging to `χ•joinedDiskValue u 0 0`'s carrier, with the
value/derivative identifications, smoothness, eventual seam support, and
vanishing near the circle and on the disk exterior. Whole-plane convergence, all-`n` smooth
with compact support (free from the exterior-vanishing clause); `fderiv` directly. -/
theorem dirichlet_piece_carrier_tendsto {A : Set Circle₁} (hA : IsOpen A)
    (u : ComplexH1) (hm : arcTrace A u = 0) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hsupp : tsupport χ ⊆ (seamDomain A hA : Set ℂ)) :
    ∃ (u_v : ComplexH1) (g : ℕ → ℂ → ℂ) (U : ℕ → ComplexH1),
      (∀ n, ContDiff ℝ ∞ (g n)) ∧
      (∀ n, ∃ δ : ℝ, 0 < δ ∧ ∀ w p : ℂ, ‖p‖ = 1 → ‖w - p‖ < δ → g n w = 0) ∧
      (∀ (n : ℕ) (w : ℂ), 1 ≤ ‖w‖ → g n w = 0) ∧
      (∀ᶠ n in atTop, tsupport (g n) ⊆ (seamDomain A hA : Set ℂ)) ∧
      Tendsto U atTop (𝓝 u_v) ∧
      ((valueCLM u_v : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
        (fun z => χ z • joinedDiskValue u 0 0 z)) ∧
      ∀ n,
        ((valueCLM (U n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] g n) ∧
        ((dxLp (U n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
          (fun z => fderiv ℝ (g n) z 1)) ∧
        ((dyLp (U n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
          (fun z => fderiv ℝ (g n) z Complex.I)) := by
  classical
  have hm' : arcTrace A u = (0 : ℂ) • arcTrace A (0 : ComplexH1) := by rw [zero_smul]; exact hm
  obtain ⟨hjet, hvlim, hVlim⟩ := weakH1_localization hχ hc hsupp
    (seamDomain_weak_gluing hA u 0 0 hm') (seamDomain_value_memLp hA u 0 0)
    (fun d => (seamDomain_jet_memLp hA u 0 0).continuousLinearMap_comp
      (ContinuousLinearMap.apply ℝ ℂ d))
  obtain ⟨u_v, hval_v, hdx_v, hdy_v⟩ :=
    carrier_of_weakJet (hjet.mono le_top) (hvlim.mono_measure Measure.restrict_le_self)
      (fun d => (hVlim d).mono_measure Measure.restrict_le_self)
  obtain ⟨hlv, hlW, f, hlf, hlfD, hCD, hδ, hext, hseam, htv, htD⟩ :=
    dirichlet_layer_approximation hA u hm hχ hc hsupp
  have hgc : ∀ n, HasCompactSupport (f n) := fun n =>
    (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset (isClosed_tsupport _)
      (closure_minimal (fun z hz => by
        rw [Metric.mem_closedBall, dist_zero_right]
        by_contra h
        exact hz (hext n z (le_of_lt (not_le.mp h)))) Metric.isClosed_closedBall)
  have hcarr : ∀ n, ∃ w : ComplexH1,
      (valueCLM w : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] f n ∧
      (dxLp w : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] (fun z => fderiv ℝ (f n) z 1) ∧
      (dyLp w : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
        (fun z => fderiv ℝ (f n) z Complex.I) :=
    fun n => smooth_compactSupport_carrier (hCD n) (hgc n)
  refine ⟨u_v, f, fun n => Classical.choose (hcarr n), hCD, hδ, hext, hseam, ?_, hval_v,
    fun n => Classical.choose_spec (hcarr n)⟩
  have toReal_conv : ∀ {F : ℕ → ℂ → ℂ} {G : ℂ → ℂ},
      Tendsto (fun n => eLpNorm (fun z => F n z - G z) 2 volume) atTop (𝓝 0) →
      Tendsto (fun n => (eLpNorm (fun z => F n z - G z) 2 volume).toReal) atTop (𝓝 0) := by
    intro F G h
    have := (ENNReal.tendsto_toReal (by simp)).comp h
    simpa [Function.comp_def] using this
  refine complexH1_tendsto_of_components ?_ ?_ ?_
  · exact component_tendsto_of_wholeplane
      (Eventually.of_forall fun n => (Classical.choose_spec (hcarr n)).1) hval_v
      (Eventually.of_forall fun n => ((hlf n).sub hlv).eLpNorm_lt_top.ne) (toReal_conv htv)
  · exact component_tendsto_of_wholeplane
      (Eventually.of_forall fun n => (Classical.choose_spec (hcarr n)).2.1) hdx_v
      (Eventually.of_forall fun n => ((hlfD n 1).sub (hlW 1)).eLpNorm_lt_top.ne) (toReal_conv (htD 1))
  · exact component_tendsto_of_wholeplane
      (Eventually.of_forall fun n => (Classical.choose_spec (hcarr n)).2.2) hdy_v
      (Eventually.of_forall fun n => ((hlfD n Complex.I).sub (hlW Complex.I)).eLpNorm_lt_top.ne)
      (toReal_conv (htD Complex.I))

/-- **Boundary pieces with either boundary condition.** For a boundary piece with cutoff `ρχ` supported
in the seam domain of `boundaryArc k m`, routed by `flag` (Neumann `true` at
`s = 1`, Dirichlet `false`), the mollified/layer approximants have `ComplexH1`
carriers converging to `ρχ • joinedDiskValue w w 1`'s carrier, exposing the
coordinate identifications and the eventual boundary conditions: whole-plane
smoothness, seam support, the puncture predicate `SuppAwayP1`, and the
flag-matched boundary clause (even parity / circle-vanishing pair). The Neumann
`SuppAwayP1` uses the whole-plane puncture hole `hP` (from `hhole`); the
Dirichlet one is free from the layer's circle-vanishing. -/
theorem boundary_piece_carrier {k : ℕ} (hk : 1 ≤ k) (w : ComplexH1)
    (flag : Bool) (m : ℕ) {ρχ : ℂ → ℝ} (hρC : ContDiff ℝ ∞ ρχ)
    (hρc : HasCompactSupport ρχ)
    (hρs : tsupport ρχ ⊆
      (seamDomain (boundaryArc k m) (isOpen_boundaryArc k m) : Set ℂ))
    (hρσ : ∀ z, ρχ (KsIndex.Bracket.σ z) = ρχ z)
    (hP : ∀ p ∈ KsIndex.Surface.punctures k, ∃ R : ℝ, 0 < R ∧
      ∀ᵐ z ∂(volume : Measure ℂ), dist z p < R → joinedDiskValue w w 1 z = 0)
    (hdir : flag = false → arcTrace (boundaryArc k m) w = 0) :
    ∃ (u_v : ComplexH1) (g : ℕ → ℂ → ℂ) (U : ℕ → ComplexH1),
      Tendsto U atTop (𝓝 u_v) ∧
      ((valueCLM u_v : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
        (fun z => ρχ z • joinedDiskValue w w 1 z)) ∧
      (∀ᶠ n in atTop,
        ((valueCLM (U n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] g n) ∧
        ((dxLp (U n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
          (fun z => fderiv ℝ (g n) z 1)) ∧
        ((dyLp (U n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
          (fun z => fderiv ℝ (g n) z Complex.I))) ∧
      (∀ᶠ n in atTop,
        ContDiff ℝ ∞ (g n) ∧
        tsupport (g n) ⊆
          (seamDomain (boundaryArc k m) (isOpen_boundaryArc k m) : Set ℂ) ∧
        KsIndex.SingleDisk.SuppAwayP1 k (closedDiskRestriction (g n)) ∧
        (flag = true → ∀ z, g n (KsIndex.Bracket.σ z) = g n z) ∧
        (flag = false → ∃ δ : ℝ, 0 < δ ∧
          (∀ v p : ℂ, ‖p‖ = 1 → ‖v - p‖ < δ → g n v = 0) ∧
          (∀ v : ℂ, 1 ≤ ‖v‖ → g n v = 0))) := by
  classical
  cases flag with
  | true =>
    have hm_neu : arcTrace (boundaryArc k m) w = (1 : ℂ) • arcTrace (boundaryArc k m) w :=
      (one_smul ℂ _).symm
    obtain ⟨u_v, U, hconv, hval, hcoord⟩ :=
      piece_carrier_tendsto (isOpen_boundaryArc k m) w 1 (one_pow 2) hm_neu hρC hρc hρs hρσ
    refine ⟨u_v, fun n => reflectionAverage 1 (compactMollify (shrinkingMollifier n)
      (fun z => ρχ z • joinedDiskValue w w 1 z)), U, hconv, hval, hcoord, ?_⟩
    have hcbase : HasCompactSupport (fun z => ρχ z • joinedDiskValue w w 1 z) :=
      hρc.smul_right
    have hsbase : tsupport (fun z => ρχ z • joinedDiskValue w w 1 z) ⊆
        (seamDomain (boundaryArc k m) (isOpen_boundaryArc k m) : Set ℂ) :=
      (tsupport_smul_subset_left ρχ _).trans hρs
    have hvl : MemLp (fun z => ρχ z • joinedDiskValue w w 1 z) 2 volume :=
      (reflected_weak_localization (isOpen_boundaryArc k m) w 1 (one_pow 2)
        hm_neu hρC hρc hρs hρσ).2.1
    have hPloc : ∀ p ∈ KsIndex.Surface.punctures k, ∃ R : ℝ, 0 < R ∧
        ∀ᵐ z ∂(volume : Measure ℂ), dist z p < R →
          (fun z => ρχ z • joinedDiskValue w w 1 z) z = 0 := by
      intro p hp
      obtain ⟨R, hR, hz⟩ := hP p hp
      refine ⟨R, hR, ?_⟩
      filter_upwards [hz] with z hzz hd
      simp only [hzz hd, smul_zero]
    filter_upwards [reflected_mollifier_support_seam 1 (isOpen_boundaryArc k m) hcbase hsbase,
      reflected_mollifier_suppAwayP1 k hk 1 hPloc] with n hseam hsupp
    refine ⟨reflectionAverage_smooth_of_zero_not_support 1
        (compactMollify_smooth (shrinkingMollifier n) hvl)
        (fun h => zero_notMem_seamDomain (isOpen_boundaryArc k m) (hseam h)),
      hseam, hsupp, ?_, ?_⟩
    · intro _ z
      have hpar := reflectionAverage_parity 1 (one_pow 2)
        (compactMollify (shrinkingMollifier n) (fun z => ρχ z • joinedDiskValue w w 1 z)) z
      simpa using hpar
    · intro h; exact absurd h (by decide)
  | false =>
    have hm_dir : arcTrace (boundaryArc k m) w = 0 := hdir rfl
    obtain ⟨u_v, g, U, hCD, hδ, hext, hseam, hconv, hval, hcoord⟩ :=
      dirichlet_piece_carrier_tendsto (isOpen_boundaryArc k m) w hm_dir hρC hρc hρs
    refine ⟨u_v, g, U, hconv, ?_, Eventually.of_forall hcoord, ?_⟩
    · filter_upwards [hval, ae_restrict_mem KsIndex.SurfaceForm.measurableSet_disk]
        with z hz hzd
      rw [hz, joined_value_on_disk w 0 0 hzd, joined_value_on_disk w w 1 hzd]
    · filter_upwards [hseam] with n hsupp
      obtain ⟨δ, hδ0, hvan⟩ := hδ n
      refine ⟨hCD n, hsupp, ?_, ?_, ?_⟩
      · refine ⟨δ, hδ0, fun v hv => ?_⟩
        obtain ⟨p, hp, hvp⟩ := hv
        have hg0 : g n v = 0 :=
          hvan v p (KsIndex.JacobiFamily.punctures_norm_eq_one hk hp) hvp
        simp [closedDiskRestriction, hg0]
      · intro h; exact absurd h (by decide)
      · intro _; exact ⟨δ, hδ0, hvan, hext n⟩

/-- A mixed-trace-domain field vanishing in a neighborhood of the punctures
is the `ComplexH1` limit of a finite sum of smooth interior and boundary
pieces. The approximants recover the value and both derivative coordinates
almost everywhere on the disk. Boundary pieces are supported away from
punctures and satisfy reflection symmetry for Neumann flags or the stated
circle/exterior vanishing conditions for Dirichlet flags. -/
theorem sIII_boundary_assembly {k : ℕ} (hk : 1 ≤ k) (b₁ b₀ : Bool) (w : ComplexH1)
    (hw : w ∈ mixedTraceDomain k b₁ b₀)
    (hhole : ∃ ρ : ℝ, 0 < ρ ∧ ∀ᵐ z ∂volume.restrict (disk : Set ℂ),
      (∃ p ∈ KsIndex.Surface.punctures k, ‖z - p‖ ≤ ρ) → valueCLM w z = 0) :
    ∃ (ι : Type) (t : Finset ι) (a : ι → ℕ) (g : ι → ℕ → ℂ → ℂ) (g₀ : ℕ → ℂ → ℂ)
      (U : ℕ → ComplexH1),
      Tendsto U atTop (𝓝 w) ∧
      (∀ᶠ n in atTop,
        ((valueCLM (U n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
          (fun z => g₀ n z + ∑ i ∈ t, g i n z)) ∧
        ((dxLp (U n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
          (fun z => fderiv ℝ (fun z => g₀ n z + ∑ i ∈ t, g i n z) z 1)) ∧
        ((dyLp (U n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
          (fun z => fderiv ℝ (fun z => g₀ n z + ∑ i ∈ t, g i n z) z Complex.I))) ∧
      (∀ᶠ n in atTop, ContDiff ℝ ∞ (g₀ n) ∧ tsupport (g₀ n) ⊆ (disk : Set ℂ)) ∧
      (∀ i ∈ t, a i = 0 ∨ a i = 1) ∧
      (∀ i ∈ t, ∀ᶠ n in atTop,
        ContDiff ℝ ∞ (g i n) ∧
        tsupport (g i n) ⊆
          (seamDomain (boundaryArc k (a i)) (isOpen_boundaryArc k (a i)) : Set ℂ) ∧
        KsIndex.SingleDisk.SuppAwayP1 k (closedDiskRestriction (g i n)) ∧
        ((if a i = 1 then b₁ else b₀) = true → ∀ z, g i n (KsIndex.Bracket.σ z) = g i n z) ∧
        ((if a i = 1 then b₁ else b₀) = false → ∃ δ : ℝ, 0 < δ ∧
          (∀ v p : ℂ, ‖p‖ = 1 → ‖v - p‖ < δ → g i n v = 0) ∧
          (∀ v : ℂ, 1 ≤ ‖v‖ → g i n v = 0))) := by
  classical
  obtain ⟨ρ, hρ0, hhole'⟩ := hhole
  set H : Set ℂ := ⋃ p ∈ KsIndex.Surface.punctures k, Metric.ball p ρ with hHdef
  have hH : IsOpen H := isOpen_biUnion (fun p _ => Metric.isOpen_ball)
  have hpH : KsIndex.Surface.punctures k ⊆ H :=
    fun p hp => Set.mem_biUnion hp (Metric.mem_ball_self hρ0)
  have hu : ∀ᵐ z ∂volume.restrict (disk : Set ℂ), z ∈ H → valueCLM w z = 0 := by
    filter_upwards [hhole'] with z hz hzH
    obtain ⟨p, hp, hpz⟩ := Set.mem_iUnion₂.mp hzH
    exact hz ⟨p, hp, by rw [← dist_eq_norm]; exact (Metric.mem_ball.mp hpz).le⟩
  obtain ⟨t, a, ha01, ρp, hρpC, hρpc, hρps, hρpσ, hone⟩ :=
    exists_punctured_boundary_partition k hH hpH
  obtain ⟨χ₀, hχ₀C, hχ₀c, hχ₀s, hvalid, -, -, -⟩ :=
    finite_weak_partition_values t ρp (fun _ => (1 : ℂ)) w hρpC hH hu hone
  -- whole-plane puncture hole for `joinedDiskValue w w 1` (used for Neumann pieces)
  have hP := joinedDiskValue_puncture_hP hk hρ0 hhole' 1
  -- arc-trace zeros for the Dirichlet-routed pieces, read off `hw`
  obtain ⟨hw1, hw0⟩ := Submodule.mem_inf.mp hw
  have key : ∀ n : ℕ, w ∈ naturalArcDomain k n false → arcTrace (boundaryArc k n) w = 0 :=
    fun n hn => LinearMap.mem_ker.mp hn
  have hdir : ∀ i : ↥(boundaryAway H), (if a i = 1 then b₁ else b₀) = false →
      arcTrace (boundaryArc k (a i)) w = 0 := by
    intro i hflag
    rcases ha01 i with h0 | h1
    · rw [h0] at hflag ⊢
      have hb : b₀ = false := by simpa using hflag
      exact key 0 (hb ▸ hw0)
    · rw [h1] at hflag ⊢
      have hb : b₁ = false := by simpa using hflag
      exact key 1 (hb ▸ hw1)
  -- per-piece dispatch (Neumann/Dirichlet) → uniform carrier families
  have hpiece : ∀ i : ↥(boundaryAway H),
      ∃ (u_v : ComplexH1) (g : ℕ → ℂ → ℂ) (U : ℕ → ComplexH1),
        Tendsto U atTop (𝓝 u_v) ∧
        ((valueCLM u_v : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
          (fun z => ρp i z • joinedDiskValue w w 1 z)) ∧
        (∀ᶠ n in atTop,
          ((valueCLM (U n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] g n) ∧
          ((dxLp (U n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
            (fun z => fderiv ℝ (g n) z 1)) ∧
          ((dyLp (U n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
            (fun z => fderiv ℝ (g n) z Complex.I))) ∧
        (∀ᶠ n in atTop,
          ContDiff ℝ ∞ (g n) ∧
          tsupport (g n) ⊆
            (seamDomain (boundaryArc k (a i)) (isOpen_boundaryArc k (a i)) : Set ℂ) ∧
          KsIndex.SingleDisk.SuppAwayP1 k (closedDiskRestriction (g n)) ∧
          ((if a i = 1 then b₁ else b₀) = true → ∀ z, g n (KsIndex.Bracket.σ z) = g n z) ∧
          ((if a i = 1 then b₁ else b₀) = false → ∃ δ : ℝ, 0 < δ ∧
            (∀ v p : ℂ, ‖p‖ = 1 → ‖v - p‖ < δ → g n v = 0) ∧
            (∀ v : ℂ, 1 ≤ ‖v‖ → g n v = 0))) :=
    fun i => boundary_piece_carrier hk w (if a i = 1 then b₁ else b₀) (a i)
      (hρpC i) (hρpc i) (hρps i) (hρpσ i) hP (hdir i)
  choose uvB gB UB hconvB hvalB hcoordB hclauseB using hpiece
  -- interior mollification
  obtain ⟨uv0, g0, U0, hg0eq, hg0sc, hconv0, hval0, hcoord0⟩ :=
    interior_piece_carrier_tendsto (Ω := KsIndex.WeakH1.disk) hχ₀C hχ₀c hχ₀s
      (carrier_hasJet w) (Lp.memLp (valueCLM w))
      (fun d => ((Lp.memLp (dxLp w)).const_smul d.re).add
        ((Lp.memLp (dyLp w)).const_smul d.im))
  refine ⟨↥(boundaryAway H), t, a, gB, g0, fun n => U0 n + ∑ i ∈ t, UB i n, ?_, ?_, ?_,
    (fun i _ => ha01 i), fun i _ => hclauseB i⟩
  · -- (A) convergence to `w`
    have hUtot : Tendsto (fun n => U0 n + ∑ i ∈ t, UB i n) atTop
        (𝓝 (uv0 + ∑ i ∈ t, uvB i)) :=
      hconv0.add (tendsto_finset_sum t (fun i _ => hconvB i))
    have hsumeq : uv0 + ∑ i ∈ t, uvB i = w := by
      apply valueCLM_injective
      apply Lp.ext
      have e1 : valueCLM (uv0 + ∑ i ∈ t, uvB i)
          = valueCLM uv0 + ∑ i ∈ t, valueCLM (uvB i) := by rw [map_add, map_sum]
      rw [e1]
      have hcomb : ∀ᵐ z ∂volume.restrict (disk : Set ℂ), ∀ i ∈ (↑t : Set _),
          (⇑(valueCLM (uvB i)) : ℂ → ℂ) z = ρp i z • joinedDiskValue w w 1 z :=
        (ae_ball_iff t.countable_toSet).2 (fun i _ => hvalB i)
      filter_upwards [Lp.coeFn_add (valueCLM uv0) (∑ i ∈ t, valueCLM (uvB i)),
        Lp.coeFn_finsetSum t (fun i => valueCLM (uvB i)), hval0, hcomb, hvalid]
        with z hadd hcsum hv0 hall hvd
      simp only [hadd, Pi.add_apply, hcsum, Finset.sum_apply, hv0]
      rw [Finset.sum_congr rfl (fun i hi => hall i (Finset.mem_coe.mpr hi))]
      exact hvd
    rw [hsumeq] at hUtot
    exact hUtot
  · -- (B) eventual coordinate identifications
    have hcoord_all : ∀ᶠ n in atTop, ∀ i ∈ t,
        ((valueCLM (UB i n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] gB i n) ∧
        ((dxLp (UB i n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
          (fun z => fderiv ℝ (gB i n) z 1)) ∧
        ((dyLp (UB i n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
          (fun z => fderiv ℝ (gB i n) z Complex.I)) :=
      (eventually_all_finset t).mpr (fun i _ => hcoordB i)
    have hclause_all : ∀ᶠ n in atTop, ∀ i ∈ t, ContDiff ℝ ∞ (gB i n) :=
      (eventually_all_finset t).mpr (fun i _ => (hclauseB i).mono (fun n h => h.1))
    filter_upwards [hcoord_all, hclause_all] with n hcall hclall
    -- the finite-sum jet rule (all pieces + interior are smooth)
    have hfderiv : ∀ z : ℂ, fderiv ℝ (fun z => g0 n z + ∑ i ∈ t, gB i n z) z
        = fderiv ℝ (g0 n) z + ∑ i ∈ t, fderiv ℝ (gB i n) z := by
      intro z
      have hd0 : HasFDerivAt (g0 n) (fderiv ℝ (g0 n) z) z :=
        (((hg0sc n).1).differentiable (by norm_num)).differentiableAt.hasFDerivAt
      have hdB : ∀ i ∈ t, HasFDerivAt (gB i n) (fderiv ℝ (gB i n) z) z :=
        fun i hi => ((hclall i hi).differentiable (by norm_num)).differentiableAt.hasFDerivAt
      exact (hd0.add (HasFDerivAt.fun_sum (fun i hi => hdB i hi))).fderiv
    refine ⟨?_, ?_, ?_⟩
    · -- value
      have e1 : valueCLM (U0 n + ∑ i ∈ t, UB i n)
          = valueCLM (U0 n) + ∑ i ∈ t, valueCLM (UB i n) := by rw [map_add, map_sum]
      rw [e1]
      have hcomb : ∀ᵐ z ∂volume.restrict (disk : Set ℂ), ∀ i ∈ (↑t : Set _),
          (⇑(valueCLM (UB i n)) : ℂ → ℂ) z = gB i n z :=
        (ae_ball_iff t.countable_toSet).2 (fun i hi => (hcall i (Finset.mem_coe.mp hi)).1)
      filter_upwards [Lp.coeFn_add (valueCLM (U0 n)) (∑ i ∈ t, valueCLM (UB i n)),
        Lp.coeFn_finsetSum t (fun i => valueCLM (UB i n)), (hcoord0 n).1, hcomb]
        with z hadd hcsum hv0 hall
      simp only [hadd, Pi.add_apply, hcsum, Finset.sum_apply, hv0]
      rw [Finset.sum_congr rfl (fun i hi => hall i (Finset.mem_coe.mpr hi))]
    · -- dx
      have e1 : dxLp (U0 n + ∑ i ∈ t, UB i n)
          = dxLp (U0 n) + ∑ i ∈ t, dxLp (UB i n) := by rw [dxLp_add, dxLp_sum]
      rw [e1]
      have hcomb : ∀ᵐ z ∂volume.restrict (disk : Set ℂ), ∀ i ∈ (↑t : Set _),
          (⇑(dxLp (UB i n)) : ℂ → ℂ) z = fderiv ℝ (gB i n) z 1 :=
        (ae_ball_iff t.countable_toSet).2 (fun i hi => (hcall i (Finset.mem_coe.mp hi)).2.1)
      filter_upwards [Lp.coeFn_add (dxLp (U0 n)) (∑ i ∈ t, dxLp (UB i n)),
        Lp.coeFn_finsetSum t (fun i => dxLp (UB i n)), (hcoord0 n).2.1, hcomb]
        with z hadd hcsum hdx0 hall
      simp only [hadd, Pi.add_apply, hcsum, Finset.sum_apply, hdx0]
      rw [Finset.sum_congr rfl (fun i hi => hall i (Finset.mem_coe.mpr hi)), hfderiv z]
      simp
    · -- dy
      have e1 : dyLp (U0 n + ∑ i ∈ t, UB i n)
          = dyLp (U0 n) + ∑ i ∈ t, dyLp (UB i n) := by rw [dyLp_add, dyLp_sum]
      rw [e1]
      have hcomb : ∀ᵐ z ∂volume.restrict (disk : Set ℂ), ∀ i ∈ (↑t : Set _),
          (⇑(dyLp (UB i n)) : ℂ → ℂ) z = fderiv ℝ (gB i n) z Complex.I :=
        (ae_ball_iff t.countable_toSet).2 (fun i hi => (hcall i (Finset.mem_coe.mp hi)).2.2)
      filter_upwards [Lp.coeFn_add (dyLp (U0 n)) (∑ i ∈ t, dyLp (UB i n)),
        Lp.coeFn_finsetSum t (fun i => dyLp (UB i n)), (hcoord0 n).2.2, hcomb]
        with z hadd hcsum hdy0 hall
      simp only [hadd, Pi.add_apply, hcsum, Finset.sum_apply, hdy0]
      rw [Finset.sum_congr rfl (fun i hi => hall i (Finset.mem_coe.mpr hi)), hfderiv z]
      simp
  · -- (C) interior piece: smooth + disk-supported (eventually)
    have hbc0 : HasCompactSupport (fun z => χ₀ z • (valueCLM w : ℂ → ℂ) z) := hχ₀c.smul_right
    have hs0 : tsupport (fun z => χ₀ z • (valueCLM w : ℂ → ℂ) z) ⊆ (disk : Set ℂ) :=
      (tsupport_smul_subset_left χ₀ _).trans hχ₀s
    filter_upwards [mollifier_support_open hbc0 disk.isOpen hs0] with n hn
    refine ⟨(hg0sc n).1, ?_⟩
    rw [hg0eq n]
    exact hn

end KsIndex.Trace
