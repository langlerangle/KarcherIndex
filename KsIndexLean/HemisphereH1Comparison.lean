module

public import KsIndexLean.HemisphereIntrinsicSmooth
public import KsIndexLean.SphericalH1Comparison

@[expose] public section


/-! The round integral H1 size on the actual lower hemisphere and its
comparison with the chart Sobolev norm. No second hemisphere is included. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace KsIndex.Spherical
open KsIndex.WeakH1

/-- Squared mass for canonical area, retaining possible divergence explicitly. -/
def hemisphereMass (u : HemisphereChartSpace) : ℝ≥0∞ :=
  ∫⁻ p in {p : Sphere | p.val 2 < 0}, ENNReal.ofReal (‖hemisphereValue u p‖ ^ 2)
    ∂(volume : Measure Ambient).toSphere

lemma hemisphereMass_eq_chart (u : HemisphereChartSpace) :
    hemisphereMass u = ∫⁻ z in (disk : Set ℂ),
      ENNReal.ofReal (‖valueCLM (hemisphereCoordinates u) z‖ ^ 2) ∂stereoAreaMeasure := by
  unfold hemisphereMass
  rw [← sphereChart_disk_eq_lower, canonicalArea_restrict,
    Set.preimage_image_eq _ sphereChart_injective,
    measurableEmbedding_sphereChart.lintegral_map]
  simp only [hemisphereValue, sphereWeakValue_pullback]

lemma hemisphereMass_comparison (u : HemisphereChartSpace) :
    ENNReal.ofReal (‖valueCLM (hemisphereCoordinates u)‖ ^ 2) ≤ hemisphereMass u ∧
    hemisphereMass u ≤ 4 * ENNReal.ofReal (‖valueCLM (hemisphereCoordinates u)‖ ^ 2) := by
  rw [hemisphereMass_eq_chart]
  simpa only [disk_L2_mass_eq_norm_sq] using
    disk_mass_comparison (valueCLM (hemisphereCoordinates u))

lemma hemisphereMass_ne_top (u : HemisphereChartSpace) : hemisphereMass u ≠ ∞ := by
  exact ne_of_lt ((hemisphereMass_comparison u).2.trans_lt
    (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top))

lemma hemisphereMass_real_comparison (u : HemisphereChartSpace) :
    ‖valueCLM (hemisphereCoordinates u)‖ ^ 2 ≤ (hemisphereMass u).toReal ∧
    (hemisphereMass u).toReal ≤ 4 * ‖valueCLM (hemisphereCoordinates u)‖ ^ 2 := by
  have h := hemisphereMass_comparison u
  constructor
  · simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using
      ENNReal.toReal_mono (hemisphereMass_ne_top u) h.1
  · simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal (sq_nonneg _)] using
      ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) h.2

/-- Intrinsic squared gradient integrated over the single lower hemisphere. -/
def hemisphereDirichletEnergy (u : HemisphereChartSpace) : ℝ :=
  ∫ p in {p : Sphere | p.val 2 < 0},
    ‖(sphereWeakGradient (hemisphereCoordinates u) p).1‖ ^ 2 +
    ‖(sphereWeakGradient (hemisphereCoordinates u) p).2‖ ^ 2
    ∂(volume : Measure Ambient).toSphere

lemma hemisphereDirichletEnergy_eq (u : HemisphereChartSpace) :
    hemisphereDirichletEnergy u = ‖dxLp (hemisphereCoordinates u)‖ ^ 2 +
      ‖dyLp (hemisphereCoordinates u)‖ ^ 2 := by
  have h := integral_re (integrable_sphereWeak_pair
    (hemisphereCoordinates u) (hemisphereCoordinates u))
  rw [← dirichlet_eq_sphere_integral] at h
  change (∫ p in sphereChart '' (disk : Set ℂ),
    (tangentPair (sphereWeakGradient (hemisphereCoordinates u) p)
      (sphereWeakGradient (hemisphereCoordinates u) p)).re
      ∂(volume : Measure Ambient).toSphere) =
    (dirichlet (hemisphereCoordinates u) (hemisphereCoordinates u)).re at h
  have hd : (dirichlet (hemisphereCoordinates u) (hemisphereCoordinates u)).re =
      ‖dxLp (hemisphereCoordinates u)‖ ^ 2 + ‖dyLp (hemisphereCoordinates u)‖ ^ 2 := by
    simp only [dirichlet, inner_self_eq_norm_sq_to_K]
    change ((‖dxLp (hemisphereCoordinates u)‖ : ℂ) ^ 2 +
      (‖dyLp (hemisphereCoordinates u)‖ : ℂ) ^ 2).re = _
    simp [pow_two]
  simpa only [hemisphereDirichletEnergy, sphereChart_disk_eq_lower,
    tangentPair_self_re, hd] using h

/-- Round H1 size, defined from canonical mass and intrinsic gradient energy. -/
def hemisphereH1Size (u : HemisphereChartSpace) : ℝ :=
  Real.sqrt ((hemisphereMass u).toReal + hemisphereDirichletEnergy u)

/-- The round and chart sizes have explicit, uniform comparison constants. -/
theorem hemisphereH1Size_comparison (u : HemisphereChartSpace) :
    ‖u‖ ≤ hemisphereH1Size u ∧ hemisphereH1Size u ≤ 2 * ‖u‖ := by
  have hm := hemisphereMass_real_comparison u
  have hn := coordinate_graph_norm_sq (hemisphereCoordinates u)
  have hi : ‖hemisphereCoordinates u‖ = ‖u‖ := hemisphereCoordinates.norm_map u
  rw [hi] at hn
  have he := hemisphereDirichletEnergy_eq u
  have hnon : 0 ≤ (hemisphereMass u).toReal + hemisphereDirichletEnergy u := by
    rw [he]
    positivity
  have hs := Real.sq_sqrt hnon
  have hp := Real.sqrt_nonneg ((hemisphereMass u).toReal + hemisphereDirichletEnergy u)
  unfold hemisphereH1Size
  constructor <;> nlinarith [sq_nonneg ‖dxLp (hemisphereCoordinates u)‖,
    sq_nonneg ‖dyLp (hemisphereCoordinates u)‖, norm_nonneg u]

/-- Smooth mixed-character approximants converge in the actual round H1
size, retaining all boundary, character and puncture conditions. -/
theorem hemisphereMixed_round_smooth_approx {k : ℕ} (hk : 1 ≤ k)
    (j : ℕ) (b1 b0 : Bool) (u : hemisphereMixedCharacterDomain k j b1 b0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : hemisphereMixedCharacterDomain k j b1 b0, ∃ f : Sphere → ℂ,
      hemisphereH1Size (v.val - u.val) < ε ∧
      hemisphereValue v.val =ᵐ[
        (volume : Measure Ambient).toSphere.restrict {p : Sphere | p.val 2 < 0}] f ∧
      (∀ p : Sphere, p.val 2 ≤ 0 → HasSmoothClosedHemisphereGerm f p) ∧
      (b1 = false → ∀ z ∈ Surface.arc k 1, f (sphereChart z) = 0) ∧
      (b0 = false → ∀ z ∈ Surface.arc k 0, f (sphereChart z) = 0) ∧
      (∀ p : Sphere, p.val 2 ≤ 0 →
        f (rotateSphere (-(2 * Real.pi) / k) p) = FormIndex.zeta k ^ j * f p) ∧
      (∃ δ > 0, ∀ p : Sphere, p.val 2 ≤ 0 →
        (∃ z ∈ Surface.punctures k, ‖stereoCoord p.val - z‖ < δ) → f p = 0) := by
  obtain ⟨v, f, hv, hf⟩ := hemisphereMixed_intrinsic_smooth_approx hk j b1 b0 u
    (half_pos hε)
  refine ⟨v, f, ?_, hf⟩
  have hb := (hemisphereH1Size_comparison (v.val - u.val)).2
  have hd : ‖v.val - u.val‖ < ε / 2 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hv
  linarith

end KsIndex.Spherical
