module

public import KsIndexLean.SphericalPotentialSmooth
public import KsIndexLean.SphericalChartOperator
public import KsIndexLean.KarcherDiskJacobiOperator
public import KsIndexLean.JacobiFamily
public import KsIndexLean.SphericalTangentTransition

@[expose] public section


/-! The spherical Schrödinger operator in the finite/infinity atlas.
The two pointwise coordinate expressions agree on their overlap. -/
noncomputable section
open Set Topology Filter
open scoped ContDiff Manifold
namespace KsIndex.Spherical
open KsIndex.WeakH1 KsIndex.KarcherData
open scoped KsIndex.KarcherData.ParameterAtlas

/-- The infinity chart pulls back the actual round metric to the same
conformal coefficient, including at its center. -/
lemma sphericalInfinityChart_metric_coefficient (z v w : ℂ) :
    inner ℝ (fderiv ℝ (fun a => (infinitySphereChart a).val) z v)
      (fderiv ℝ (fun a => (infinitySphereChart a).val) z w) =
      stereoAreaDensity z * inner ℝ v w := by
  have hd : fderiv ℝ (fun a => (infinitySphereChart a).val) z =
      (fderiv ℝ (fun a => (southChart a).val) ((starRingEnd ℂ) z)).comp
        Complex.conjCLE.toContinuousLinearMap :=
    by
      simpa only [infinitySphereChart, Function.comp_def, Complex.conjCLE_apply] using
        (Complex.conjCLE.comp_right_fderiv (f := fun a => (southChart a).val) (x := z))
  rw [hd]
  simp only [ContinuousLinearMap.comp_apply, Complex.conjCLE_apply,
    ContinuousLinearEquiv.coe_coe, fderiv_southPoint_apply,
    reflectAmbient_inner, fderiv_stereoPoint_inner, stereoAreaDensity_eq]
  simpa only [Complex.norm_conj, Complex.conjLIE_apply] using
    congrArg (fun a : ℝ => 4 / (1 + ‖z‖ ^ 2) ^ 2 * a)
      (Complex.conjLIE.inner_map_map v w)

/-- The flat Laplacian under the holomorphic inversion of the sphere atlas. -/
lemma laplacian_comp_inv {f : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0)
    (hf : ContDiffAt ℝ 2 f z⁻¹) :
    Surface.laplacian (fun w => f w⁻¹) z =
      ((‖z‖⁻¹ ^ 4 : ℝ) : ℂ) * Surface.laplacian f z⁻¹ := by
  have hc : ContDiffAt ℝ 2 (f ∘ (starRingEnd ℂ)) (Bracket.σ z) := by
    have hf' : ContDiffAt ℝ 2 f ((starRingEnd ℂ) (Bracket.σ z)) := by
      simpa [Bracket.σ] using hf
    exact hf'.comp _ Complex.conjCLE.contDiff.contDiffAt
  have h := EndChart.laplacian_comp_sigma hz hc
  have he : (f ∘ (starRingEnd ℂ)) ∘ Bracket.σ = fun w => f w⁻¹ := by
    funext w
    simp [Function.comp_def, Bracket.σ]
  rw [he, laplacian_comp_conj] at h
  simpa [Bracket.σ] using h

/-- Round area density has exactly the weight needed for inversion. -/
lemma stereoAreaDensity_inv {z : ℂ} (hz : z ≠ 0) :
    stereoAreaDensity z⁻¹ * ‖z‖⁻¹ ^ 4 = stereoAreaDensity z := by
  simpa [stereoAreaDensity_eq, Bracket.σ] using stereoAreaDensity_sigma hz

/-- The potential is unchanged by holomorphic inversion. -/
lemma spherePotential_chart_inv {k : ℕ} (hk : 2 ≤ k) {z : ℂ} (hz : z ≠ 0) :
    spherePotential (surfacePotential k) (sphereChart z⁻¹) =
      spherePotential (surfacePotential k) (sphereChart z) := by
  rw [← infinitySphereChart_overlap hz]
  exact spherePotential_infinity_pullback hk z

/-- The stereographic operator transforms as a scalar under chart change. -/
theorem sphericalChartJacobiOperator_inv {k : ℕ} (hk : 2 ≤ k)
    {f : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0) (hf : ContDiffAt ℝ 2 f z⁻¹) :
    sphericalChartJacobiOperator k (fun w => f w⁻¹) z =
      sphericalChartJacobiOperator k f z⁻¹ := by
  unfold sphericalChartJacobiOperator
  rw [conformalLaplaceBeltrami_eq (Eventually.of_forall
    (fun w => ne_of_gt (stereoAreaDensity_pos w))),
    conformalLaplaceBeltrami_eq (Eventually.of_forall
    (fun w => ne_of_gt (stereoAreaDensity_pos w))), laplacian_comp_inv hz hf,
    spherePotential_chart_inv hk hz]
  have hd : (stereoAreaDensity z : ℂ) =
      (stereoAreaDensity z⁻¹ : ℂ) * ((‖z‖⁻¹ ^ 4 : ℝ) : ℂ) := by
    exact_mod_cast (stereoAreaDensity_inv hz).symm
  rw [hd]
  have hw : (((‖z‖⁻¹ ^ 4 : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero 4 (inv_ne_zero (norm_ne_zero_iff.mpr hz)))
  rw [mul_inv_rev]
  congr 1
  calc
    _ = (((‖z‖⁻¹ ^ 4 : ℝ) : ℂ)⁻¹ * ((‖z‖⁻¹ ^ 4 : ℝ) : ℂ)) *
        ((stereoAreaDensity z⁻¹ : ℂ)⁻¹ * Surface.laplacian f z⁻¹) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hw, one_mul]

/-- The coordinate expression depends only on the germ of the function. -/
lemma sphericalChartJacobiOperator_congr {k : ℕ} {f g : ℂ → ℂ} {z : ℂ}
    (h : f =ᶠ[𝓝 z] g) :
    sphericalChartJacobiOperator k f z = sphericalChartJacobiOperator k g z := by
  rw [sphericalChartJacobiOperator_eq, sphericalChartJacobiOperator_eq,
    JacobiFamily.laplacian_congr h, h.self_of_nhds]

/-- Pointwise spherical operator, using the finite chart except at its missing pole. -/
def sphereJacobiOperator (k : ℕ) (f : Sphere → ℂ) (p : Sphere) : ℂ := by
  classical
  exact if p ∈ ParameterAtlas.finite.source then
    sphericalChartJacobiOperator k (f ∘ sphereChart) (ParameterAtlas.finite p)
  else
    sphericalChartJacobiOperator k (f ∘ infinitySphereChart) (ParameterAtlas.infinity p)

/-- The finite-chart formula holds at every finite coordinate, including zero. -/
lemma sphereJacobiOperator_finite (k : ℕ) (f : Sphere → ℂ) (z : ℂ) :
    sphereJacobiOperator k f (sphereChart z) =
      sphericalChartJacobiOperator k (f ∘ sphereChart) z := by
  have hz : sphereChart z ∈ ParameterAtlas.finite.source := ⟨z, mem_univ _, rfl⟩
  simp [sphereJacobiOperator, hz]

/-- The infinity expression agrees on the overlap with the finite expression. -/
lemma sphericalChartJacobiOperator_overlap {k : ℕ} (hk : 2 ≤ k)
    (f : Sphere → ℂ) {z : ℂ} (hz : z ≠ 0)
    (hf : ContDiffAt ℝ 2 (f ∘ sphereChart) z⁻¹) :
    sphericalChartJacobiOperator k (f ∘ infinitySphereChart) z =
      sphericalChartJacobiOperator k (f ∘ sphereChart) z⁻¹ := by
  have he : (f ∘ infinitySphereChart) =ᶠ[𝓝 z]
      (fun w => (f ∘ sphereChart) w⁻¹) := by
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw
    simp [infinitySphereChart_overlap hw]
  rw [sphericalChartJacobiOperator_congr he]
  exact sphericalChartJacobiOperator_inv hk hz hf

/-- The infinity formula includes its center, so the global operator is defined
at both poles without evaluating an inverse coordinate at a singularity. -/
theorem sphereJacobiOperator_infinity {k : ℕ} (hk : 2 ≤ k)
    (f : Sphere → ℂ) (hf : ContDiff ℝ 2 (f ∘ sphereChart)) (z : ℂ) :
    sphereJacobiOperator k f (infinitySphereChart z) =
      sphericalChartJacobiOperator k (f ∘ infinitySphereChart) z := by
  by_cases hz : z = 0
  · subst z
    simp [sphereJacobiOperator, ParameterAtlas.infinity_zero_not_finite]
  · rw [infinitySphereChart_overlap hz, sphereJacobiOperator_finite]
    exact (sphericalChartJacobiOperator_overlap hk f hz hf.contDiffAt).symm

/-- Smooth spherical functions have smooth finite-coordinate representatives. -/
lemma contDiff_sphereChart_pullback {f : Sphere → ℂ}
    (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f) :
    ContDiff ℝ ∞ (f ∘ sphereChart) := by
  have hc : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ sphereChart := by
    intro z
    apply contMDiffAt_symm_of_mem_maximalAtlas (e := ParameterAtlas.finite)
    · apply IsManifold.subset_maximalAtlas
      change ParameterAtlas.finite ∈ ({ParameterAtlas.finite, ParameterAtlas.infinity} : Set _)
      simp
    · exact mem_univ z
  exact (hf.comp hc).contDiff

/-- The global operator has the infinity-coordinate formula for every smooth
spherical function, including at the north pole. -/
theorem sphereJacobiOperator_infinity_smooth {k : ℕ} (hk : 2 ≤ k)
    {f : Sphere → ℂ} (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f) (z : ℂ) :
    sphereJacobiOperator k f (infinitySphereChart z) =
      sphericalChartJacobiOperator k (f ∘ infinitySphereChart) z := by
  exact sphereJacobiOperator_infinity hk f
    ((contDiff_sphereChart_pullback hf).of_le (by simp)) z

/-- In either chart the operator is round Laplace–Beltrami plus the same
global smooth potential, with no exceptional pole value. -/
theorem sphereJacobiOperator_chart_formulas {k : ℕ} (hk : 2 ≤ k)
    {f : Sphere → ℂ} (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f) (z : ℂ) :
    (sphereJacobiOperator k f (sphereChart z) =
      conformalLaplaceBeltrami stereoAreaDensity (f ∘ sphereChart) z +
        (spherePotential (surfacePotential k) (sphereChart z) : ℂ) * f (sphereChart z)) ∧
    (sphereJacobiOperator k f (infinitySphereChart z) =
      conformalLaplaceBeltrami stereoAreaDensity (f ∘ infinitySphereChart) z +
        (spherePotential (surfacePotential k) (infinitySphereChart z) : ℂ) *
          f (infinitySphereChart z)) := by
  constructor
  · rw [sphereJacobiOperator_finite]; rfl
  · rw [sphereJacobiOperator_infinity_smooth hk hf,
      spherePotential_infinity_pullback hk]
    rfl

/-- The two chart formulas determine the spherical operator uniquely. -/
theorem sphereJacobiOperator_unique (k : ℕ) (f : Sphere → ℂ) (g : Sphere → ℂ)
    (hfin : ∀ z, g (sphereChart z) = sphericalChartJacobiOperator k (f ∘ sphereChart) z)
    (hinf : ∀ z, g (infinitySphereChart z) =
      sphericalChartJacobiOperator k (f ∘ infinitySphereChart) z) :
    g = sphereJacobiOperator k f := by
  funext p
  by_cases hp : p ∈ ParameterAtlas.finite.source
  · obtain ⟨z, _, rfl⟩ := hp
    exact (hfin z).trans (sphereJacobiOperator_finite k f z).symm
  · have hn : p.val 2 = 1 := by
      by_contra h
      exact hp ⟨stereoCoord p.val, mem_univ _, Subtype.ext (stereoPoint_stereoCoord p h)⟩
    rw [north_unique p hn]
    simpa [sphereJacobiOperator, ParameterAtlas.infinity_zero_not_finite] using hinf 0

end KsIndex.Spherical
