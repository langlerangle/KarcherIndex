module

public import KsIndexLean.KarcherMetricTensor
public import KsIndexLean.KarcherCenteredChartGeometry
public import KsIndexLean.JacobiFields

@[expose] public section


/-!
# Riemannian area density of the actual EW chart

The local area density of the EW immersion chart, DERIVED from its Gram matrix (first fundamental
form) as `√(E·G − F²)`, and proved to equal the conformal factor `ρ_k²` in disk coordinates. This is
the genuine geometric derivation from the actual differential, not the model's by-definition `ρ²`
weight: the Gram matrix of the real EW differential is `ρ_k²·Id` (E = G = ρ_k², F = 0), whence the
area density `√(ρ_k⁴) = ρ_k²`. The `ρ_k²`-weighted disk measure `ewAreaMeasure` is supplied as the
`withDensity` interface for later global integration.
-/
noncomputable section
open Complex MeasureTheory Filter
open scoped Topology
namespace KsIndex.KarcherData

/-- Gram determinant `E·G − F²` of a chart `X : ℂ → AmbientTriple` at `w`, from its first
fundamental form (the induced metric pulled back along the real differential). -/
def chartGramDet (X : ℂ → AmbientTriple) (w : ℂ) : ℝ :=
  firstFundamentalForm X w 1 1 * firstFundamentalForm X w Complex.I Complex.I
    - firstFundamentalForm X w 1 Complex.I ^ 2

/-- Local Riemannian area density `√(E·G − F²)` of a chart. -/
def chartAreaDensity (X : ℂ → AmbientTriple) (w : ℂ) : ℝ :=
  Real.sqrt (chartGramDet X w)

/-- For a chart conformal at `w` with factor `s` (`euclideanSq (fderiv X w v) = s‖v‖²`), the Gram
determinant is `s²` (the Gram matrix is `s·Id`: `E = G = s`, `F = 0`). -/
lemma chartGramDet_of_conformal {X : ℂ → AmbientTriple} {w : ℂ} {s : ℝ}
    (hm : ∀ v : ℂ, euclideanSq (fderiv ℝ X w v) = s * ‖v‖ ^ 2) :
    chartGramDet X w = s ^ 2 := by
  have hE : firstFundamentalForm X w 1 1 = s := by
    simp only [firstFundamentalForm]; rw [euclideanDot_of_conformal hm]; simp
  have hF : firstFundamentalForm X w 1 Complex.I = 0 := by
    simp only [firstFundamentalForm]; rw [euclideanDot_of_conformal hm]; simp
  have hG : firstFundamentalForm X w Complex.I Complex.I = s := by
    simp only [firstFundamentalForm]; rw [euclideanDot_of_conformal hm]; simp
  simp only [chartGramDet, hE, hF, hG]; ring

/-- Area density of a conformal chart (factor `s ≥ 0`) is exactly `s`. -/
lemma chartAreaDensity_of_conformal {X : ℂ → AmbientTriple} {w : ℂ} {s : ℝ} (hs : 0 ≤ s)
    (hm : ∀ v : ℂ, euclideanSq (fderiv ℝ X w v) = s * ‖v‖ ^ 2) :
    chartAreaDensity X w = s := by
  rw [chartAreaDensity, chartGramDet_of_conformal hm, Real.sqrt_sq hs]

/-- **Area density of the actual EW chart = ρ_k²**, derived from the Gram matrix of the real EW
differential — not posited. -/
lemma chartAreaDensity_ew {k : ℕ} (hk : 2 ≤ k) {X : ℂ → AmbientTriple} {w : ℂ}
    (hX : HasFDerivAt X (ewRealDifferential k w) w) :
    chartAreaDensity X w = Surface.rho k w ^ 2 := by
  refine chartAreaDensity_of_conformal (by positivity) (fun v => ?_)
  rw [hX.fderiv]; exact ewRealDifferential_metric hk w v

open scoped KsIndex.KarcherData.ParameterAtlas KsIndex.KarcherData.PeriodicAmbient
namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- The actual centered EW immersion chart has area density `ρ_k²` at each finite chart center. -/
lemma centeredChart_areaDensity (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : HeightLift.projection q = finiteParameter w) :
    chartAreaDensity (R.centeredChart q) w.val = Surface.rho k w.val ^ 2 :=
  chartAreaDensity_ew h.out (R.centeredChart_finite_differential q w hq)

end PaperHalfPeriodRealization

/-- The EW area measure in disk coordinates: the flat planar volume weighted by `ρ_k²` (the area
density). This is the `withDensity` interface for later global integration; on the open disk the weight is
the actual chart area density `chartAreaDensity_ew`. -/
def ewAreaMeasure (k : ℕ) : Measure ℂ :=
  volume.withDensity (fun w => ENNReal.ofReal (Surface.rho k w ^ 2))

/-- **Seam/overlap null.** The unit circle `‖w‖ = 1` — the disk-chain
seam locus — is `ewAreaMeasure`-null: `ewAreaMeasure` is absolutely continuous w.r.t. planar volume
(it is a `withDensity`), and the circle is a measure-zero sphere in the plane. So the `2m` disk
interiors partition the glued quotient up to an `ewAreaMeasure`-null set (the sphere-pole analog of
`stereoAreaMeasure_ae_ne_zero`). -/
lemma ewAreaMeasure_unitCircle_null {k : ℕ} :
    ewAreaMeasure k {w : ℂ | ‖w‖ = 1} = 0 := by
  have hs : {w : ℂ | ‖w‖ = 1} = Metric.sphere (0 : ℂ) 1 :=
    Set.ext fun w => (mem_sphere_zero_iff_norm).symm
  rw [hs]
  simp only [ewAreaMeasure]
  exact withDensity_absolutelyContinuous volume _ (Measure.addHaar_sphere volume 0 1)

/-- `ewAreaMeasure` is exactly the flat volume weighted by the actual EW chart area density, for any
chart realizing the EW differential on a set (e.g. the disk immersion). -/
lemma ewAreaMeasure_eq_withDensity_areaDensity {k : ℕ} (hk : 2 ≤ k)
    {X : ℂ → AmbientTriple} {U : Set ℂ} (hX : ∀ w ∈ U, HasFDerivAt X (ewRealDifferential k w) w) :
    ∀ w ∈ U, (fun w => ENNReal.ofReal (Surface.rho k w ^ 2)) w
      = ENNReal.ofReal (chartAreaDensity X w) := by
  intro w hw
  rw [chartAreaDensity_ew hk (hX w hw)]

/-! ## Inverse-metric gradient density -/

/-- Inverse-metric gradient density `(g⁻¹)^{ij} ⟨∂ᵢ f, ∂ⱼ f⟩` of a ℂ-valued `f` in a chart, from the
explicit 2×2 inverse of the Gram matrix (first fundamental form `g`). -/
def chartInvMetricGradSq (X : ℂ → AmbientTriple) (f : ℂ → ℂ) (w : ℂ) : ℝ :=
  (firstFundamentalForm X w Complex.I Complex.I * ‖fderiv ℝ f w 1‖ ^ 2
      - 2 * firstFundamentalForm X w 1 Complex.I
        * ((fderiv ℝ f w 1).re * (fderiv ℝ f w Complex.I).re
          + (fderiv ℝ f w 1).im * (fderiv ℝ f w Complex.I).im)
      + firstFundamentalForm X w 1 1 * ‖fderiv ℝ f w Complex.I‖ ^ 2)
    / chartGramDet X w

/-- For a chart conformal at `w` with factor `s ≠ 0`, the inverse-metric gradient density is
`s⁻¹` times the flat gradient density (the inverse Gram matrix is `s⁻¹·Id`). -/
lemma chartInvMetricGradSq_of_conformal {X : ℂ → AmbientTriple} {w : ℂ} {s : ℝ} {f : ℂ → ℂ}
    (hs : s ≠ 0) (hm : ∀ v : ℂ, euclideanSq (fderiv ℝ X w v) = s * ‖v‖ ^ 2) :
    chartInvMetricGradSq X f w = s⁻¹ * Surface.gradSq f w := by
  have hE : firstFundamentalForm X w 1 1 = s := by
    simp only [firstFundamentalForm]; rw [euclideanDot_of_conformal hm]; simp
  have hFc : firstFundamentalForm X w 1 Complex.I = 0 := by
    simp only [firstFundamentalForm]; rw [euclideanDot_of_conformal hm]; simp
  have hG : firstFundamentalForm X w Complex.I Complex.I = s := by
    simp only [firstFundamentalForm]; rw [euclideanDot_of_conformal hm]; simp
  simp only [chartInvMetricGradSq, chartGramDet, Surface.gradSq, hE, hFc, hG]
  field_simp
  ring

/-- **Inverse-metric gradient density of the actual EW chart = ρ_k⁻²·(flat density)**, derived from
the inverse of the actual Gram matrix (not posited as the model `gradSq/ρ²`). -/
lemma chartInvMetricGradSq_ew {k : ℕ} (hk : 2 ≤ k) {X : ℂ → AmbientTriple} {w : ℂ}
    (hw : w ∉ Surface.punctures k) (hX : HasFDerivAt X (ewRealDifferential k w) w) (f : ℂ → ℂ) :
    chartInvMetricGradSq X f w = (Surface.rho k w ^ 2)⁻¹ * Surface.gradSq f w := by
  refine chartInvMetricGradSq_of_conformal (rho_sq_pos hk hw).ne' (fun v => ?_)
  rw [hX.fderiv]; exact ewRealDifferential_metric hk w v

/-! ## Conformal invariance of the Dirichlet energy density

The 2D conformal invariance of the Dirichlet energy, as a chartwise density identity — the
mathematical heart of why the geometric EW index/nullity reduces to the model (flat) problem:
`|∇_g f|²_g · dA_g = |∇f|² · dA`, i.e. the inverse-metric gradient density times the area density is
the FLAT gradient density, the conformal factor cancelling. Design-independent of the global measure
assembly; it feeds the geometric-form ↔ model-form identification. -/

/-- Conformal invariance: for a chart conformal at `w` with factor `s > 0`,
`chartInvMetricGradSq · chartAreaDensity = gradSq` (`s⁻¹·gradSq · s = gradSq`). -/
lemma chartDirichletDensity_of_conformal {X : ℂ → AmbientTriple} {w : ℂ} {s : ℝ} {f : ℂ → ℂ}
    (hs : 0 < s) (hm : ∀ v : ℂ, euclideanSq (fderiv ℝ X w v) = s * ‖v‖ ^ 2) :
    chartInvMetricGradSq X f w * chartAreaDensity X w = Surface.gradSq f w := by
  rw [chartInvMetricGradSq_of_conformal hs.ne' hm, chartAreaDensity_of_conformal hs.le hm,
    mul_right_comm, inv_mul_cancel₀ hs.ne', one_mul]

/-- **The actual EW chart: the geometric Dirichlet energy density is the flat one** —
`(ρ_k⁻²·gradSq)·ρ_k² = gradSq`, derived from the actual Gram matrix. -/
lemma chartDirichletDensity_ew {k : ℕ} (hk : 2 ≤ k) {X : ℂ → AmbientTriple} {w : ℂ}
    (hw : w ∉ Surface.punctures k) (hX : HasFDerivAt X (ewRealDifferential k w) w) (f : ℂ → ℂ) :
    chartInvMetricGradSq X f w * chartAreaDensity X w = Surface.gradSq f w :=
  chartDirichletDensity_of_conformal (rho_sq_pos hk hw)
    (fun v => by rw [hX.fderiv]; exact ewRealDifferential_metric hk w v)

/-- **Potential density of the actual EW chart = `potV`**: `absA² · ρ² = potV` with
`ρ² = chartAreaDensity`, so the geometric Jacobi potential term `|A|²_g · dA_g` has flat density
`potV`. Together with `chartDirichletDensity_ew` this is the full integrand-level fidelity — the
geometric Jacobi form density equals the model `gradSq − potV·|f|²`, both halves chartwise with the
conformal factor already cancelled. -/
lemma chartPotentialDensity_ew {k : ℕ} (hk : 2 ≤ k) {X : ℂ → AmbientTriple} {w : ℂ}
    (hw : w ∉ Surface.punctures k) (hX : HasFDerivAt X (ewRealDifferential k w) w) :
    Surface.absA k w ^ 2 * chartAreaDensity X w = Surface.potV k w := by
  rw [chartAreaDensity_ew hk hX]
  exact KsIndex.JacobiFields.absA_sq_mul_rho_sq hk hw

/-! ## Coordinate Laplace–Beltrami -/

/-- Conformal-metric Laplace–Beltrami in divergence form, for conformal factor `c = √det g` (metric
`g = c·Id`): `Δ_g f = (1/c)·∂ᵢ(√g gⁱʲ ∂ⱼ f)`. The `i`-th flux weight `√g gⁱᵢ = c·c⁻¹` is written
explicitly so the reduction below is a derivation, not a definition of `Δ_g := c⁻¹·Δ`. -/
def conformalLaplaceBeltrami (c : ℂ → ℝ) (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  (↑(c w))⁻¹ * (fderiv ℝ (fun z => (↑(c z) * (↑(c z))⁻¹ : ℂ) * fderiv ℝ f z 1) w 1
    + fderiv ℝ (fun z => (↑(c z) * (↑(c z))⁻¹ : ℂ) * fderiv ℝ f z Complex.I) w Complex.I)

/-- **Divergence-form reduction.** Where `c ≠ 0` on a neighborhood of `w`, the flux weight
`√g gⁱʲ = c·c⁻¹ = δ` is constant, so the Laplace–Beltrami reduces to `(1/c)·laplacian` with no
derivative of `c` — the 2D conformal identity, derived (the neighborhood hypothesis matters). -/
lemma conformalLaplaceBeltrami_eq {c : ℂ → ℝ} {f : ℂ → ℂ} {w : ℂ} (hc : ∀ᶠ z in 𝓝 w, c z ≠ 0) :
    conformalLaplaceBeltrami c f w = (↑(c w))⁻¹ * Surface.laplacian f w := by
  have hcong : ∀ d : ℂ, (fun z => (↑(c z) * (↑(c z))⁻¹ : ℂ) * fderiv ℝ f z d)
      =ᶠ[𝓝 w] (fun z => fderiv ℝ f z d) := fun d => by
    filter_upwards [hc] with z hz
    rw [mul_inv_cancel₀ (by exact_mod_cast hz : (↑(c z) : ℂ) ≠ 0), one_mul]
  simp only [conformalLaplaceBeltrami, Surface.laplacian]
  rw [(hcong 1).fderiv_eq, (hcong Complex.I).fderiv_eq]

/-- **Divergence-form Laplace–Beltrami of the PRESCRIBED EW conformal metric field `z ↦ ρ_k(z)²`
reduces to `laplacianG` (`= ρ_k⁻²·laplacian`)**, on a neighborhood where `ρ_k² ≠ 0` (e.g. the open
disk). This is the operator reduction for the metric FIELD `ρ_k²·Id`; identifying it with the
intrinsic Laplace–Beltrami of a FIXED centered chart additionally needs that chart's Gram field to
equal `ρ_k²·Id` on a neighborhood — the atlas `centeredChart_*_metric` lemmas give conformality only
at each chart's own center; the neighborhood FIELD version is supplied in `KarcherChartMetricField`
(see the note below). -/
lemma conformalLaplaceBeltrami_ew {k : ℕ} {w : ℂ} (f : ℂ → ℂ)
    (hc : ∀ᶠ z in 𝓝 w, Surface.rho k z ^ 2 ≠ 0) :
    conformalLaplaceBeltrami (fun z => Surface.rho k z ^ 2) f w = Surface.laplacianG k f w := by
  rw [conformalLaplaceBeltrami_eq hc]
  simp only [Surface.laplacianG, Complex.ofReal_inv]

/-! ## Actual-chart applications at finite chart centers -/

/-- `ρ_k² ≠ 0` on a neighborhood of any finite (non-puncture) parameter — the puncture set is
closed, so its open complement is a neighborhood where `ρ_k² > 0`. Discharges the neighborhood
hypothesis of `conformalLaplaceBeltrami_eq` at finite chart centers. -/
lemma rho_sq_eventually_ne {k : ℕ} (hk : 2 ≤ k) {w : ℂ} (hw : w ∉ Surface.punctures k) :
    ∀ᶠ z in 𝓝 w, Surface.rho k z ^ 2 ≠ 0 := by
  have hpc : IsClosed (Surface.punctures k) :=
    isClosed_eq (continuous_id.pow (2 * k)) continuous_const
  filter_upwards [hpc.isOpen_compl.mem_nhds hw] with z hz
  exact (rho_sq_pos hk hz).ne'

/-- Laplace–Beltrami of the conformal EW metric at any finite parameter equals the model
`laplacianG` (`= ρ_k⁻²·laplacian`) — the finite-chart-center instance of the general `_ew` lemma. -/
lemma laplaceBeltrami_ew_finite {k : ℕ} (hk : 2 ≤ k) {w : ℂ} (hw : w ∉ Surface.punctures k)
    (f : ℂ → ℂ) :
    conformalLaplaceBeltrami (fun z => Surface.rho k z ^ 2) f w = Surface.laplacianG k f w :=
  conformalLaplaceBeltrami_ew f (rho_sq_eventually_ne hk hw)

namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- Inverse-metric gradient density of the ACTUAL centered chart at a finite chart center:
`ρ_k⁻²·gradSq`. -/
lemma centeredChart_invMetricGradSq (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : HeightLift.projection q = finiteParameter w) (f : ℂ → ℂ) :
    chartInvMetricGradSq (R.centeredChart q) f w.val
      = (Surface.rho k w.val ^ 2)⁻¹ * Surface.gradSq f w.val :=
  chartInvMetricGradSq_ew h.out w.property (R.centeredChart_finite_differential q w hq) f

/-- Area density of the actual centered chart at an INFINITY chart center (odd-copy center,
coordinate `0`): `ρ_k(0)²` — the disk-coordinate `ρ` at `0` (the inversion symmetry gives the same
`ρ`, not a finite-`w` formula evaluated at `∞`). -/
lemma centeredChart_areaDensity_infinity (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (hq : HeightLift.projection q = infinityParameter k) :
    chartAreaDensity (R.centeredChart q) 0 = Surface.rho k 0 ^ 2 :=
  chartAreaDensity_of_conformal (by positivity) (R.centeredChart_infinity_metric q hq)

/-- Inverse-metric gradient density of the actual centered chart at an infinity chart center
(coordinate `0`): `ρ_k(0)⁻²·gradSq`. -/
lemma centeredChart_invMetricGradSq_infinity (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (hq : HeightLift.projection q = infinityParameter k) (f : ℂ → ℂ) :
    chartInvMetricGradSq (R.centeredChart q) f 0 = (Surface.rho k 0 ^ 2)⁻¹ * Surface.gradSq f 0 :=
  chartInvMetricGradSq_of_conformal (rho_sq_pos h.out (zero_not_puncture h.out)).ne'
    (R.centeredChart_infinity_metric q hq)

/-- Conformal invariance on the actual centered chart at a finite center: the geometric
Dirichlet energy density equals the flat one. -/
lemma centeredChart_dirichletDensity_finite (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : HeightLift.projection q = finiteParameter w) (f : ℂ → ℂ) :
    chartInvMetricGradSq (R.centeredChart q) f w.val * chartAreaDensity (R.centeredChart q) w.val
      = Surface.gradSq f w.val :=
  chartDirichletDensity_ew h.out w.property (R.centeredChart_finite_differential q w hq) f

/-- Conformal invariance on the actual centered ∞-chart (coordinate `0`). -/
lemma centeredChart_dirichletDensity_infinity (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (hq : HeightLift.projection q = infinityParameter k) (f : ℂ → ℂ) :
    chartInvMetricGradSq (R.centeredChart q) f 0 * chartAreaDensity (R.centeredChart q) 0
      = Surface.gradSq f 0 :=
  chartDirichletDensity_of_conformal (rho_sq_pos h.out (zero_not_puncture h.out))
    (R.centeredChart_infinity_metric q hq)

/-- Potential density on the actual centered chart at a finite center: `absA²·ρ² = potV`. -/
lemma centeredChart_potentialDensity_finite (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : HeightLift.projection q = finiteParameter w) :
    Surface.absA k w.val ^ 2 * chartAreaDensity (R.centeredChart q) w.val
      = Surface.potV k w.val := by
  rw [R.centeredChart_areaDensity q w hq]
  exact KsIndex.JacobiFields.absA_sq_mul_rho_sq h.out w.property

/-- Potential density on the actual centered ∞-chart (coordinate `0`). -/
lemma centeredChart_potentialDensity_infinity (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (hq : HeightLift.projection q = infinityParameter k) :
    Surface.absA k 0 ^ 2 * chartAreaDensity (R.centeredChart q) 0 = Surface.potV k 0 := by
  rw [R.centeredChart_areaDensity_infinity q hq]
  exact KsIndex.JacobiFields.absA_sq_mul_rho_sq h.out (zero_not_puncture h.out)

/-- The PRESCRIBED-`ρ_k²`-field divergence-form Laplace–Beltrami at coordinate `0` (the
infinity chart's center coordinate) reduces to `laplacianG` — the `w=0` instance of
`laplaceBeltrami_ew_finite` (`0 ∉ punctures`). NOTE: this concerns the metric FIELD, not the actual
fixed ∞-chart's Gram field, and carries no `R`/`q`; the intrinsic ∞-chart LB identification needs
the neighborhood link below. -/
lemma laplaceBeltrami_ew_infinity_center (f : ℂ → ℂ) :
    conformalLaplaceBeltrami (fun z => Surface.rho k z ^ 2) f 0 = Surface.laplacianG k f 0 :=
  laplaceBeltrami_ew_finite h.out (zero_not_puncture h.out) f

/-! ### Neighborhood metric link — supplied in `KarcherChartMetricField`

The area (`centeredChart_areaDensity`/`_infinity`) and inverse-gradient
(`centeredChart_invMetricGradSq`/`_infinity`) identities are POINTWISE at the chart center — all a
pointwise density needs, and they genuinely consume the actual differential/metric
there. The Laplace–Beltrami, however, is a divergence-form DIFFERENTIAL operator whose coefficient
functions sit under the derivatives, so identifying the intrinsic LB of a FIXED centered chart
`R.centeredChart q` with `laplacianG` additionally requires the FIELD identity

  `∀ᶠ z in 𝓝 center, firstFundamentalForm (R.centeredChart q) z a b = ρ_k(ψ z)² ⟪a, b⟫`

i.e. the fixed chart's Gram matrix equals `ρ_k²·Id` on a NEIGHBORHOOD, not merely at its own
center (the trunk atlas lemmas `centeredChart_metric`/`_metric_tensor`/`_finite_metric`,
`centeredChart_infinity_metric` supply only the center value). This neighborhood FIELD identity is
now supplied in `KarcherChartMetricField` (`centeredChart_finite_metric_field`,
`centeredChart_infinity_metric_field`), where `conformalLaplaceBeltrami_ew` consumes it verbatim
(with `ρ_k²` as the field) to give the actual-chart intrinsic Laplace–Beltrami
(`centeredChart_finite_laplaceBeltrami`, `centeredChart_infinity_laplaceBeltrami`), hence the
geometric Jacobi operator. -/

end PaperHalfPeriodRealization

end KsIndex.KarcherData
