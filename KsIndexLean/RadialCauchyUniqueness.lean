module

public import KsIndexLean.SphericalEigenModeRegularity
public import Mathlib.Analysis.ODE.ExistUnique

@[expose] public section


noncomputable section
open Set
open scoped NNReal
namespace KsIndex.Trace

lemma radialSystem_lipschitz (p q : ℝ) (K : ℝ≥0)
    (hp : ‖p‖ ≤ K) (hq : ‖q‖ ≤ K) :
    LipschitzWith K (fun x : ℂ × ℂ => (p • x.2, q • x.1)) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simp only [Prod.dist_eq, dist_smul₀]
  apply max_le
  · exact mul_le_mul hp (le_max_right _ _) dist_nonneg K.coe_nonneg
  · exact mul_le_mul hq (le_max_left _ _) dist_nonneg K.coe_nonneg

/-- Uniqueness for the mode/flux system on a closed annulus, from Cauchy data
at an interior radius. The continuous coefficients need not be explicit. -/
lemma radialSystem_zero_of_cauchy {a b t₀ : ℝ} (p q : ℝ → ℝ)
    (hp : ContinuousOn p (Icc a b)) (hq : ContinuousOn q (Icc a b))
    (f g : ℝ → ℂ) (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hdf : ∀ t ∈ Ioo a b, HasDerivAt f (p t • g t) t)
    (hdg : ∀ t ∈ Ioo a b, HasDerivAt g (q t • f t) t)
    (ht : t₀ ∈ Ioo a b) (hf0 : f t₀ = 0) (hg0 : g t₀ = 0) :
    ∀ t ∈ Icc a b, f t = 0 ∧ g t = 0 := by
  obtain ⟨P, hP⟩ := isCompact_Icc.exists_bound_of_continuousOn hp
  obtain ⟨Q, hQ⟩ := isCompact_Icc.exists_bound_of_continuousOn hq
  let K : ℝ≥0 := ⟨max 0 (max P Q), le_max_left _ _⟩
  have hl (t : ℝ) (ht : t ∈ Ioo a b) :
      LipschitzOnWith K (fun x : ℂ × ℂ => (p t • x.2, q t • x.1)) Set.univ := by
    apply (radialSystem_lipschitz (p t) (q t) K ?_ ?_).lipschitzOnWith
    · exact (hP t (Ioo_subset_Icc_self ht)).trans ((le_max_left P Q).trans (le_max_right _ _))
    · exact (hQ t (Ioo_subset_Icc_self ht)).trans ((le_max_right P Q).trans (le_max_right _ _))
  have he := ODE_solution_unique_of_mem_Icc hl ht (hf.prodMk hg)
    (fun t ht => (hdf t ht).prodMk (hdg t ht)) (fun _ _ => Set.mem_univ _)
    (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℂ × ℂ)) (Icc a b))
    (fun t _ => by
      have hz : (p t • (0 : ℂ × ℂ).2, q t • (0 : ℂ × ℂ).1) = (0 : ℂ × ℂ) := by ext <;> simp
      rw [hz]
      exact hasDerivAt_const t (0 : ℂ × ℂ))
    (fun _ _ => Set.mem_univ _) (by simp [hf0, hg0])
  intro t ht
  have h := he ht
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

open KsIndex.WeakH1 KsIndex.Spherical

/-- The actual weak eigenmode vanishes on a closed annulus if its mode and
flux vanish at one interior radius. -/
lemma sphericalEigen_mode_zero_of_cauchy {a b t₀ : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (k : ℕ) (lam : ℝ)
    (u : ComplexH1) (n : ℤ)
    (hu : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v))
    (ht : t₀ ∈ Ioo a b) (hf : interiorDiskMode hab u n t₀ = 0)
    (hg : eigenDiskFluxRepresentative hab k lam u n t₀ = 0) :
    ∀ t ∈ Icc a b, interiorDiskMode hab u n t = 0 ∧
      eigenDiskFluxRepresentative hab k lam u n t = 0 := by
  apply radialSystem_zero_of_cauchy (fun t => t⁻¹)
    (fun t => (n : ℝ)^2 / t - t * sphericalEigenRadialCoefficient k lam t)
    (continuousOn_id.inv₀ (fun t ht => (ha.trans_le ht.1).ne'))
    ((continuousOn_const.div continuousOn_id (fun t ht => (ha.trans_le ht.1).ne')).sub
      (continuousOn_id.mul (sphericalEigenRadialCoefficient_smooth k lam).continuous.continuousOn))
    (interiorDiskMode hab u n) (eigenDiskFluxRepresentative hab k lam u n)
    (interiorDiskMode_continuousOn ha hab hb u n)
    (eigenDiskFluxRepresentative_continuousOn ha hab hb k lam u n)
    (fun t ht => eigenDiskMode_hasDerivAt ha hab hb k lam u n hu ht)
    (fun t ht => eigenDiskFluxRepresentative_hasDerivAt ha hab hb k lam u n ht)
    ht hf hg

end KsIndex.Trace
