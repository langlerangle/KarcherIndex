module

public import KsIndexLean.KarcherChartArea
public import KsIndexLean.KarcherCenteredChartGerm
public import KsIndexLean.KarcherGlobalMap
public import KsIndexLean.KarcherFixedInfinityGeometry

@[expose] public section


/-! # Fixed-chart metric fields and intrinsic Laplace–Beltrami operators

For `k ≥ 2`, the metric of a fixed centered chart agrees with `ρ_k(z)²·Id`
on a neighborhood of its center. This neighborhood identity is needed because
the coefficients of the divergence-form Laplace–Beltrami operator occur under
derivatives.

The centered-chart germ and local Enneper–Weierstrass primitives identify the
chart locally with a constant translate of a primitive. Their derivatives agree
throughout a neighborhood, giving the conformal metric and area-density fields.
The same argument applies at infinity using the inversion coordinate. Local
agreement of the area density with `ρ_k²` then identifies the intrinsic operator
with `laplacianG` at the chart center. -/

noncomputable section
open Set Topology Filter
open scoped ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
  KsIndex.KarcherData.PeriodicAmbient
namespace KsIndex.KarcherData

/-- `conformalLaplaceBeltrami` sees the conformal factor only through a neighborhood of the point
(the factor enters under a `fderiv`), so eventually-equal factors give the same operator value. -/
lemma conformalLaplaceBeltrami_congr {c₁ c₂ : ℂ → ℝ} {f : ℂ → ℂ} {w : ℂ}
    (hc : c₁ =ᶠ[𝓝 w] c₂) :
    conformalLaplaceBeltrami c₁ f w = conformalLaplaceBeltrami c₂ f w := by
  have hw : c₁ w = c₂ w := hc.eq_of_nhds
  have h1 : (fun z => (↑(c₁ z) * (↑(c₁ z))⁻¹ : ℂ) * fderiv ℝ f z 1)
      =ᶠ[𝓝 w] (fun z => (↑(c₂ z) * (↑(c₂ z))⁻¹ : ℂ) * fderiv ℝ f z 1) := by
    filter_upwards [hc] with z hz; rw [hz]
  have hI : (fun z => (↑(c₁ z) * (↑(c₁ z))⁻¹ : ℂ) * fderiv ℝ f z Complex.I)
      =ᶠ[𝓝 w] (fun z => (↑(c₂ z) * (↑(c₂ z))⁻¹ : ℂ) * fderiv ℝ f z Complex.I) := by
    filter_upwards [hc] with z hz; rw [hz]
  simp only [conformalLaplaceBeltrami, hw, h1.fderiv_eq, hI.fderiv_eq]

open scoped KsIndex.KarcherData.ParameterAtlas KsIndex.KarcherData.PeriodicAmbient
namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- **Neighborhood metric field, finite chart.** The actual fixed centered chart's conformal metric
is `ρ_k(z)²·Id` as a FIELD on a neighborhood of a finite chart center — not just at the center. -/
lemma centeredChart_finite_metric_field (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : HeightLift.projection q = finiteParameter w) :
    ∀ᶠ z in 𝓝 w.val, ∀ d : ℂ,
      euclideanSq (fderiv ℝ (R.centeredChart q) z d) = Surface.rho k z ^ 2 * ‖d‖ ^ 2 := by
  obtain ⟨r, hr, X, _, hs, _, hd, he, _, _⟩ :=
    extendedEWMap_finite_local_geometry h.out (reflectionBasepoint k) w R.C
  have hw : w.val ∈ Metric.ball w.val r := Metric.mem_ball_self hr
  have hb := Metric.isOpen_ball.mem_nhds hw
  have hX : ContDiffAt ℝ ∞ X w.val := hs.contDiffAt hb
  have hg : (extendedEWMap h.out (reflectionBasepoint k) R.C ∘
      (chartAt ℂ (finiteParameter w)).symm) =ᶠ[𝓝 w.val]
      (fun z => extendedEWMap h.out (reflectionBasepoint k) R.C (finiteParameter w) +
        projectPeriod (X z)) := by
    filter_upwards [ParameterAtlas.finite_chart_inverse_germ w, hb] with z hz hzr
    let p := (chartAt ℂ (finiteParameter w)).symm z
    have ha : z ∉ Surface.punctures k := by
      intro hzp
      exact p.property ⟨z, hzp, hz.symm⟩
    have hp : finiteParameter (⟨z, ha⟩ : PuncturedPlane k) = p := Subtype.ext hz.symm
    change extendedEWMap h.out (reflectionBasepoint k) R.C p = _
    rw [← hp]
    exact he ⟨z, ha⟩ hzr
  have hX' : ContinuousAt X (R.chartCenter q) := by
    rw [R.chartCenter_finite q w hq]
    exact hX.continuousAt
  have hg' := hg
  rw [← hq, ← R.chartCenter_finite q w hq] at hg'
  obtain ⟨t, ht⟩ := R.centeredChart_germ q X _ hX' hg'
  rw [R.chartCenter_finite q w hq] at ht
  filter_upwards [ht.eventually_nhds, hb] with z hz_ee hz_ball
  intro d
  have hee : R.centeredChart q =ᶠ[𝓝 z] (fun y => t + X y) := hz_ee
  rw [show fderiv ℝ (R.centeredChart q) z = ewRealDifferential k z from
    hee.fderiv_eq.trans ((hd z hz_ball).const_add t).fderiv]
  exact ewRealDifferential_metric h.out z d

/-- **Neighborhood metric field, infinity chart.** The actual fixed centered chart's conformal
metric is `ρ_k(z)²·Id` as a FIELD on a neighborhood of coordinate `0` (the infinity chart center);
`ρ` is the same disk-coordinate formula, via the inversion symmetry. -/
lemma centeredChart_infinity_metric_field (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (hq : HeightLift.projection q = infinityParameter k) :
    ∀ᶠ z in 𝓝 (0 : ℂ), ∀ d : ℂ,
      euclideanSq (fderiv ℝ (R.centeredChart q) z d) = Surface.rho k z ^ 2 * ‖d‖ ^ 2 := by
  obtain ⟨r, hr0, hr1, X, _, hs, _, hd, he, _⟩ :=
    exists_fixed_infinity_geometry (reflectionBasepoint k) R.C R.hC
  have hw : (0 : ℂ) ∈ Metric.ball 0 r := Metric.mem_ball_self hr0
  have hb := Metric.isOpen_ball.mem_nhds hw
  have hX : ContDiffAt ℝ ∞ X 0 := hs.contDiffAt hb
  have hg : (extendedEWMap h.out (reflectionBasepoint k) R.C ∘
      (chartAt ℂ (infinityParameter k)).symm) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => R.C + projectPeriod (X z)) := by
    filter_upwards [ParameterAtlas.infinity_chart_inverse_germ (k := k), hb] with z hz hzr
    have hp : (chartAt ℂ (infinityParameter k)).symm z =
        infinityParameterChart h.out hr1.le ⟨z, hzr⟩ := Subtype.ext hz
    change extendedEWMap h.out (reflectionBasepoint k) R.C _ = _
    rw [hp]
    exact he ⟨z, hzr⟩
  have hX' : ContinuousAt X (R.chartCenter q) := by
    rw [R.chartCenter_infinity q hq]
    exact hX.continuousAt
  have hg' := hg
  rw [← hq, ← R.chartCenter_infinity q hq] at hg'
  obtain ⟨t, ht⟩ := R.centeredChart_germ q X R.C hX' hg'
  rw [R.chartCenter_infinity q hq] at ht
  filter_upwards [ht.eventually_nhds, hb] with z hz_ee hz_ball
  intro d
  have hee : R.centeredChart q =ᶠ[𝓝 z] (fun y => t + X y) := hz_ee
  rw [show fderiv ℝ (R.centeredChart q) z = infinityRealDifferential k z from
    hee.fderiv_eq.trans ((hd z hz_ball).const_add t).fderiv]
  exact infinityRealDifferential_metric h.out z d

/-- Area-density FIELD at a finite chart center: `chartAreaDensity (R.centeredChart q) z = ρ_k(z)²`
on a neighborhood (from the neighborhood metric field). -/
lemma centeredChart_finite_areaDensity_field (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : HeightLift.projection q = finiteParameter w) :
    (fun z => chartAreaDensity (R.centeredChart q) z) =ᶠ[𝓝 w.val]
      (fun z => Surface.rho k z ^ 2) := by
  filter_upwards [R.centeredChart_finite_metric_field q w hq] with z hz
  exact chartAreaDensity_of_conformal (by positivity) hz

/-- Area-density FIELD at the infinity chart center (coordinate `0`). -/
lemma centeredChart_infinity_areaDensity_field (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (hq : HeightLift.projection q = infinityParameter k) :
    (fun z => chartAreaDensity (R.centeredChart q) z) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => Surface.rho k z ^ 2) := by
  filter_upwards [R.centeredChart_infinity_metric_field q hq] with z hz
  exact chartAreaDensity_of_conformal (by positivity) hz

/-- **Intrinsic Laplace–Beltrami of the actual finite chart = `laplacianG`.** The divergence-form
operator built from the chart's OWN area-density field (`√det g`) reduces to `laplacianG`, because
that field equals `ρ_k²` on a neighborhood (`centeredChart_finite_areaDensity_field`) and
`conformalLaplaceBeltrami` sees the factor only through a neighborhood. -/
lemma centeredChart_finite_laplaceBeltrami (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : HeightLift.projection q = finiteParameter w) (f : ℂ → ℂ) :
    conformalLaplaceBeltrami (fun z => chartAreaDensity (R.centeredChart q) z) f w.val
      = Surface.laplacianG k f w.val := by
  rw [conformalLaplaceBeltrami_congr (R.centeredChart_finite_areaDensity_field q w hq)]
  exact laplaceBeltrami_ew_finite h.out w.property f

/-- **Intrinsic Laplace–Beltrami of the actual infinity chart = `laplacianG`** (coordinate `0`). -/
lemma centeredChart_infinity_laplaceBeltrami (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (hq : HeightLift.projection q = infinityParameter k) (f : ℂ → ℂ) :
    conformalLaplaceBeltrami (fun z => chartAreaDensity (R.centeredChart q) z) f 0
      = Surface.laplacianG k f 0 := by
  rw [conformalLaplaceBeltrami_congr (R.centeredChart_infinity_areaDensity_field q hq)]
  exact laplaceBeltrami_ew_finite h.out (zero_not_puncture h.out) f

end PaperHalfPeriodRealization
end KsIndex.KarcherData
