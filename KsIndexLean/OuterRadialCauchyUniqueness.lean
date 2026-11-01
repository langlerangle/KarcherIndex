module

public import KsIndexLean.RadialCauchyUniqueness
public import Mathlib.Analysis.Calculus.FDeriv.Extend

@[expose] public section


noncomputable section
open Set Filter
open scoped NNReal Topology
namespace KsIndex.Trace

/-- Continuous interior derivative extends to the left derivative at the
outer endpoint. This supplies, rather than assumes, endpoint regularity. -/
lemma closedInterval_left_derivative {a b : ℝ} (hab : a < b)
    {f g : ℝ → ℂ} (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (g t) t) :
    ∀ t ∈ Ioc a b, HasDerivWithinAt f (g t) (Iic t) t := by
  intro t ht
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · exact (hd t ⟨ht.1, hlt⟩).hasDerivWithinAt
  · subst t
    apply hasDerivWithinAt_Iic_of_tendsto_deriv
      (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
      ((hf b ⟨hab.le, le_rfl⟩).mono Ioo_subset_Icc_self) (Ioo_mem_nhdsLT hab)
    have hg' : Tendsto g (𝓝[<] b) (𝓝 (g b)) := by
      have h := hg b ⟨hab.le, le_rfl⟩
      rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsLE hab] at h
      exact h.mono_left (nhdsWithin_mono _ Iio_subset_Iic_self)
    apply hg'.congr'
    filter_upwards [Ioo_mem_nhdsLT hab] with t ht
    exact (hd t ht).deriv.symm

lemma radialSystem_zero_of_outer_cauchy {a b : ℝ} (p q : ℝ → ℝ)
    (hp : ContinuousOn p (Icc a b)) (hq : ContinuousOn q (Icc a b))
    (f g : ℝ → ℂ) (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hdf : ∀ t ∈ Ioo a b, HasDerivAt f (p t • g t) t)
    (hdg : ∀ t ∈ Ioo a b, HasDerivAt g (q t • f t) t)
    (hab : a < b) (hf0 : f b = 0) (hg0 : g b = 0) :
    ∀ t ∈ Icc a b, f t = 0 ∧ g t = 0 := by
  obtain ⟨P, hP⟩ := isCompact_Icc.exists_bound_of_continuousOn hp
  obtain ⟨Q, hQ⟩ := isCompact_Icc.exists_bound_of_continuousOn hq
  let K : ℝ≥0 := ⟨max 0 (max P Q), le_max_left _ _⟩
  have hl (t : ℝ) (ht : t ∈ Ioc a b) :
      LipschitzOnWith K (fun x : ℂ × ℂ => (p t • x.2, q t • x.1)) Set.univ := by
    apply (radialSystem_lipschitz (p t) (q t) K ?_ ?_).lipschitzOnWith
    · exact (hP t (Ioc_subset_Icc_self ht)).trans ((le_max_left P Q).trans (le_max_right _ _))
    · exact (hQ t (Ioc_subset_Icc_self ht)).trans ((le_max_right P Q).trans (le_max_right _ _))
  have he := ODE_solution_unique_of_mem_Icc_left hl (hf.prodMk hg)
    (fun t ht => (closedInterval_left_derivative hab hf (hp.smul hg) hdf t ht).prodMk
      (closedInterval_left_derivative hab hg (hq.smul hf) hdg t ht)) (fun _ _ => Set.mem_univ _)
    (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℂ × ℂ)) (Icc a b))
    (fun t _ => by
      have hz : (p t • (0 : ℂ × ℂ).2, q t • (0 : ℂ × ℂ).1) = (0 : ℂ × ℂ) := by ext <;> simp
      rw [hz]
      exact (hasDerivAt_const t (0 : ℂ × ℂ)).hasDerivWithinAt)
    (fun _ _ => Set.mem_univ _) (by simp [hf0, hg0])
  intro t ht
  have h := he ht
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

open KsIndex.WeakH1 KsIndex.Spherical

/-- The actual weak eigenmode vanishes on a closed annulus if its mode and
flux vanish at the outer endpoint. -/
lemma sphericalEigen_mode_zero_of_outer_cauchy {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (k : ℕ) (lam : ℝ)
    (u : ComplexH1) (n : ℤ)
    (hu : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v))
    (hf : interiorDiskMode hab u n b = 0)
    (hg : eigenDiskFluxRepresentative hab k lam u n b = 0) :
    ∀ t ∈ Icc a b, interiorDiskMode hab u n t = 0 ∧
      eigenDiskFluxRepresentative hab k lam u n t = 0 := by
  apply radialSystem_zero_of_outer_cauchy (fun t => t⁻¹)
    (fun t => (n : ℝ)^2 / t - t * sphericalEigenRadialCoefficient k lam t)
    (continuousOn_id.inv₀ (fun t ht => (ha.trans_le ht.1).ne'))
    ((continuousOn_const.div continuousOn_id (fun t ht => (ha.trans_le ht.1).ne')).sub
      (continuousOn_id.mul (sphericalEigenRadialCoefficient_smooth k lam).continuous.continuousOn))
    (interiorDiskMode hab u n) (eigenDiskFluxRepresentative hab k lam u n)
    (interiorDiskMode_continuousOn ha hab hb u n)
    (eigenDiskFluxRepresentative_continuousOn ha hab hb k lam u n)
    (fun t ht => eigenDiskMode_hasDerivAt ha hab hb k lam u n hu ht)
    (fun t ht => eigenDiskFluxRepresentative_hasDerivAt ha hab hb k lam u n ht)
    hab hf hg

end KsIndex.Trace
