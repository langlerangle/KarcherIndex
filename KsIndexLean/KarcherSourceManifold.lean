module

public import KsIndexLean.KarcherTargetManifold

@[expose] public section


/-! The holomorphic finite/infinity atlas on the EW parameter sphere. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold
namespace KsIndex.KarcherData.ParameterAtlas

def finite : OpenPartialHomeomorph Spherical.Sphere ℂ :=
  (isOpenEmbedding_sphereChart.toOpenPartialHomeomorph Spherical.sphereChart).symm

def infinity : OpenPartialHomeomorph Spherical.Sphere ℂ :=
  (isOpenEmbedding_infinitySphereChart.toOpenPartialHomeomorph infinitySphereChart).symm

@[simp] lemma finite_symm (z : ℂ) : finite.symm z = Spherical.sphereChart z := rfl
@[simp] lemma infinity_symm (z : ℂ) : infinity.symm z = infinitySphereChart z := rfl
@[simp] lemma finite_apply (z : ℂ) : finite (Spherical.sphereChart z) = z :=
  isOpenEmbedding_sphereChart.toOpenPartialHomeomorph_left_inv _
@[simp] lemma infinity_apply (z : ℂ) : infinity (infinitySphereChart z) = z :=
  isOpenEmbedding_infinitySphereChart.toOpenPartialHomeomorph_left_inv _

lemma infinity_zero_not_finite : infinitySphereChart 0 ∉ finite.source := by
  rintro ⟨z, _, hz⟩
  exact Spherical.stereoPoint_third_ne_one z
    ((congrArg (fun p : Spherical.Sphere => p.val 2) hz).trans infinitySphereChart_zero_height)

lemma finite_zero_not_infinity : Spherical.sphereChart 0 ∉ infinity.source := by
  rintro ⟨z, _, hz⟩
  by_cases h : z = 0
  · subst z
    exact infinity_zero_not_finite (hz ▸ (show Spherical.sphereChart 0 ∈ finite.source from ⟨0, mem_univ _, rfl⟩))
  · rw [infinitySphereChart_overlap h] at hz
    exact (inv_ne_zero h) (Spherical.sphereChart_injective hz)

lemma finite_infinity_change {z : ℂ} (hz : infinity.symm z ∈ finite.source) :
    finite (infinity.symm z) = z⁻¹ := by
  have hn : z ≠ 0 := by rintro rfl; exact infinity_zero_not_finite hz
  rw [infinity_symm, infinitySphereChart_overlap hn, finite_apply]

lemma infinity_finite_change {z : ℂ} (hz : finite.symm z ∈ infinity.source) :
    infinity (finite.symm z) = z⁻¹ := by
  have hn : z ≠ 0 := by rintro rfl; exact finite_zero_not_infinity hz
  have he : Spherical.sphereChart z = infinitySphereChart z⁻¹ := by
    rw [infinitySphereChart_overlap (inv_ne_zero hn), inv_inv]
  rw [finite_symm, he, infinity_apply]

scoped instance sphereChartedSpace : ChartedSpace ℂ Spherical.Sphere := by
  classical
  exact {
    atlas := {finite, infinity}
    chartAt p := if p ∈ finite.source then finite else infinity
    mem_chart_source p := by
      split_ifs with h
      · exact h
      · have hp : p.val 2 = 1 := by
          by_contra hn
          exact h ⟨Spherical.stereoCoord p.val, mem_univ _,
            Subtype.ext (Spherical.stereoPoint_stereoCoord p hn)⟩
        exact ⟨0, mem_univ _, (north_unique p hp).symm⟩
    chart_mem_atlas p := by split_ifs <;> simp }

scoped instance sphereSmoothManifold : IsManifold 𝓘(ℝ, ℂ) ∞ Spherical.Sphere := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  change e ∈ ({finite, infinity} : Set _) at he
  change e' ∈ ({finite, infinity} : Set _) at he'
  simp only [mem_insert_iff, mem_singleton_iff] at he he'
  rcases he with rfl | rfl <;> rcases he' with rfl | rfl
  · intro z hz
    simp only [mfld_simps] at hz ⊢
    have he : (fun w => finite (finite.symm w)) = fun w : ℂ => w := by
      funext w; exact finite_apply w
    simp only [Function.comp_def]
    rw [he]
    exact contDiffAt_id.contDiffWithinAt
  · intro z hz
    simp only [mfld_simps] at hz ⊢
    have hn : z ≠ 0 := by rintro rfl; exact finite_zero_not_infinity hz.2
    exact ((contDiffAt_id.inv hn).contDiffWithinAt).congr
      (fun w hw => infinity_finite_change hw.2) (infinity_finite_change hz.2)
  · intro z hz
    simp only [mfld_simps] at hz ⊢
    have hn : z ≠ 0 := by rintro rfl; exact infinity_zero_not_finite hz.2
    exact ((contDiffAt_id.inv hn).contDiffWithinAt).congr
      (fun w hw => finite_infinity_change hw.2) (finite_infinity_change hz.2)
  · intro z hz
    simp only [mfld_simps] at hz ⊢
    have he : (fun w => infinity (infinity.symm w)) = fun w : ℂ => w := by
      funext w; exact infinity_apply w
    simp only [Function.comp_def]
    rw [he]
    exact contDiffAt_id.contDiffWithinAt

/-- The punctured parameter carrier inherits the finite/infinity atlas as an open submanifold. -/
def parameterOpen {k : ℕ} (hk : 2 ≤ k) : TopologicalSpace.Opens Spherical.Sphere :=
  ⟨(Spherical.sphereChart '' Surface.punctures k)ᶜ, isOpen_parameterSphere hk⟩

scoped instance parameterChartedSpace {k : ℕ} [h : Fact (2 ≤ k)] :
    ChartedSpace ℂ (ParameterSphere k) :=
  inferInstanceAs (ChartedSpace ℂ (parameterOpen h.out))

scoped instance parameterSmoothManifold {k : ℕ} [h : Fact (2 ≤ k)] :
    IsManifold 𝓘(ℝ, ℂ) ∞ (ParameterSphere k) :=
  inferInstanceAs (IsManifold 𝓘(ℝ, ℂ) ∞ (parameterOpen h.out))

lemma sphere_chartAt_finite (z : ℂ) :
    chartAt ℂ (Spherical.sphereChart z) = finite := by
  classical
  change (if Spherical.sphereChart z ∈ finite.source then finite else infinity) = finite
  exact ite_eq_left ⟨z, mem_univ _, rfl⟩

lemma sphere_chartAt_infinity : chartAt ℂ (infinitySphereChart 0) = infinity := by
  classical
  change (if infinitySphereChart 0 ∈ finite.source then finite else infinity) = infinity
  exact ite_eq_right infinity_zero_not_finite

lemma parameter_chartAt_finite {k : ℕ} [Fact (2 ≤ k)] (w : PuncturedPlane k) :
    chartAt ℂ (finiteParameter w) (finiteParameter w) = w.val := by
  change chartAt ℂ (Spherical.sphereChart w.val) (Spherical.sphereChart w.val) = w.val
  rw [sphere_chartAt_finite, finite_apply]

lemma parameter_chartAt_infinity {k : ℕ} [Fact (2 ≤ k)] :
    chartAt ℂ (infinityParameter k) (infinityParameter k) = 0 := by
  change chartAt ℂ (infinitySphereChart 0) (infinitySphereChart 0) = 0
  rw [sphere_chartAt_infinity, infinity_apply]

lemma finite_chart_inverse_germ {k : ℕ} [h : Fact (2 ≤ k)] (w : PuncturedPlane k) :
    (fun z => ((chartAt ℂ (finiteParameter w)).symm z).val) =ᶠ[𝓝 w.val]
      Spherical.sphereChart := by
  have he := (parameterOpen h.out).chartAt_subtype_val_symm_eventuallyEq
    (H := ℂ) (x := (finiteParameter w : parameterOpen h.out))
  simp only [finiteParameter, sphere_chartAt_finite, finite_apply] at he
  exact he.symm

lemma infinity_chart_inverse_germ {k : ℕ} [h : Fact (2 ≤ k)] :
    (fun z => ((chartAt ℂ (infinityParameter k)).symm z).val) =ᶠ[𝓝 (0 : ℂ)]
      infinitySphereChart := by
  have he := (parameterOpen h.out).chartAt_subtype_val_symm_eventuallyEq
    (H := ℂ) (x := (infinityParameter k : parameterOpen h.out))
  simp only [infinityParameter, sphere_chartAt_infinity, infinity_apply] at he
  exact he.symm

end KsIndex.KarcherData.ParameterAtlas
