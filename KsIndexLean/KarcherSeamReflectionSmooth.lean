module

public import KsIndexLean.KarcherLowerSeamGerm

@[expose] public section


/-! Real smoothness of the EW parameter seam reflection, including both poles. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold
namespace KsIndex.KarcherData
open scoped ParameterAtlas

lemma sphereChart_contMDiff :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ Spherical.sphereChart := by
  intro z
  have h := contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := ∞)
    (x := Spherical.sphereChart 0)
  rw [ParameterAtlas.sphere_chartAt_finite] at h
  exact h.contMDiffAt (by change Set.univ ∈ 𝓝 z; exact Filter.univ_mem)

lemma infinitySphereChart_contMDiff :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ infinitySphereChart := by
  intro z
  have h := contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := ∞)
    (x := infinitySphereChart 0)
  rw [ParameterAtlas.sphere_chartAt_infinity] at h
  exact h.contMDiffAt (by change Set.univ ∈ 𝓝 z; exact Filter.univ_mem)

lemma reflectSphere_contMDiff :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ Spherical.reflectSphere := by
  have hc : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (starRingEnd ℂ) := by
    apply ContDiff.contMDiff
    exact Complex.conjCLE.contDiff
  intro p
  rw [contMDiffAt_iff_source]
  simp only [mfld_simps]
  change ContMDiffWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
    (Spherical.reflectSphere ∘ (chartAt ℂ p).symm) Set.univ (chartAt ℂ p p)
  rw [contMDiffWithinAt_univ]
  classical
  by_cases hp : p ∈ ParameterAtlas.finite.source
  · have he : chartAt ℂ p = ParameterAtlas.finite := ite_eq_left hp
    rw [he]
    have hfun : Spherical.reflectSphere ∘ ParameterAtlas.finite.symm =
        infinitySphereChart ∘ (starRingEnd ℂ) := by
      funext z
      change Spherical.southChart z = Spherical.southChart (starRingEnd ℂ (starRingEnd ℂ z))
      rw [starRingEnd_self_apply]
    rw [hfun]
    exact (infinitySphereChart_contMDiff.comp hc) _
  · have he : chartAt ℂ p = ParameterAtlas.infinity := ite_eq_right hp
    rw [he]
    have hfun : Spherical.reflectSphere ∘ ParameterAtlas.infinity.symm =
        Spherical.sphereChart ∘ (starRingEnd ℂ) := by
      funext z
      exact Spherical.reflectSphere_involutive _
    rw [hfun]
    exact (sphereChart_contMDiff.comp hc) _

lemma parameterSeamReflection_contMDiff {k : ℕ} [h : Fact (2 ≤ k)] :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (parameterSeamReflection h.out) := by
  apply (ContMDiff.subtypeVal_comp_iff (ParameterAtlas.parameterOpen h.out)
    (parameterSeamReflection h.out)).mp
  exact reflectSphere_contMDiff.comp
    (contMDiff_subtype_val (U := ParameterAtlas.parameterOpen h.out))

/-- Precomposition by the seam reflection preserves and reflects smoothness. -/
lemma contMDiffAt_comp_seamReflection_iff {k : ℕ} [h : Fact (2 ≤ k)]
    (f : ParameterSphere k → ℂ) (p : ParameterSphere k) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (f ∘ parameterSeamReflection h.out) p ↔
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f (parameterSeamReflection h.out p) := by
  constructor
  · intro hf
    have hf' : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (f ∘ parameterSeamReflection h.out)
        (parameterSeamReflection h.out (parameterSeamReflection h.out p)) := by
      rw [parameterSeamReflection_involutive h.out p]
      exact hf
    have hs := hf'.comp (parameterSeamReflection h.out p)
      (parameterSeamReflection_contMDiff (parameterSeamReflection h.out p))
    have he : (f ∘ parameterSeamReflection h.out) ∘ parameterSeamReflection h.out = f := by
      funext x
      change f (parameterSeamReflection h.out (parameterSeamReflection h.out x)) = f x
      rw [parameterSeamReflection_involutive h.out x]
    rw [he] at hs
    exact hs
  · intro hf
    exact hf.comp p (parameterSeamReflection_contMDiff p)

end KsIndex.KarcherData
