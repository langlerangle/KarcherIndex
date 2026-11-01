module

public import KsIndexLean.GeneralDirichletEigenvalue
public import KsIndexLean.WeakCharacterReconstruction
public import KsIndexLean.GroundStateDirichlet

@[expose] public section


/-!
# Nonnegativity of the full Dirichlet problem

The positive vertical Jacobi field gives nonnegativity on compactly supported
smooth tests. Density transfers this bound to the full Dirichlet space, with
the spherical bulk mass unchanged.
-/
noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.FormIndex KsIndex.Spherical

lemma surfaceJacobi_character_sum {k : ℕ} (hk : 0 < k) (u : ComplexH1) :
    weakJacobi (surfacePotential k) u u =
      ∑ r : Fin k, weakJacobi (surfacePotential k)
        (carrierCharProj k r u) (carrierCharProj k r u) := by
  let p := fun r : Fin k => carrierCharProj k r u
  have hl (v : ComplexH1) :
      weakJacobi (surfacePotential k) (∑ r, p r) v =
        ∑ r, weakJacobi (surfacePotential k) (p r) v := by
    let L : ComplexH1 →ₛₗ[starRingEnd ℂ] ℂ :=
      { toFun := fun w => weakJacobi (surfacePotential k) w v
        map_add' := fun a b => weakJacobi_add_left _ a b v
        map_smul' := fun c a => weakJacobi_smul_left _ c a v }
    exact map_sum L _ _
  have hr (v : ComplexH1) :
      weakJacobi (surfacePotential k) v (∑ r, p r) =
        ∑ r, weakJacobi (surfacePotential k) v (p r) := by
    let L : ComplexH1 →ₗ[ℂ] ℂ :=
      { toFun := weakJacobi (surfacePotential k) v
        map_add' := weakJacobi_add_right _ v
        map_smul' := fun c a => weakJacobi_smul_right _ c v a }
    exact map_sum L _ _
  calc
    _ = weakJacobi (surfacePotential k) (∑ r, p r) (∑ r, p r) := by
      rw [show (∑ r, p r) = u from carrierCharProj_sum hk u]
    _ = ∑ r, ∑ s, weakJacobi (surfacePotential k) (p r) (p s) := by
      rw [hl]; simp_rw [hr]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_eq_single r
      · intro s _ hsr
        exact surfaceJacobi_distinct_characters hk r s (Ne.symm hsr) _ _
          (carrierCharProj_mem_character hk r u) (carrierCharProj_mem_character hk s u)
      · simp

lemma fullDirichlet_form_nonnegative {k : ℕ} (hk : 3 ≤ k)
    (u : ComplexH1) (hu : u ∈ zeroTraceDomain Set.univ) :
    0 ≤ (weakJacobi (surfacePotential k) u u).re := by
  exact KsIndex.GroundState.fullDirichlet_nonnegative_ground_state (by omega) u hu


local instance dirichletLowestInner : InnerProductSpace ℂ (zeroTraceDomain Set.univ) :=
  diskDomain_innerProductSpace _
local instance dirichletLowestComplete : CompleteSpace (zeroTraceDomain Set.univ) :=
  (isClosed_zeroTraceDomain Set.univ).completeSpace_coe

lemma fullDirichlet_eigenvalue_nonnegative {k : ℕ} (hk : 3 ≤ k) (lam : ℝ)
    (u : zeroTraceDomain Set.univ) (hne : u ≠ 0)
    (hu : u ∈ diskWeakEigenspace (zeroTraceDomain Set.univ) (surfacePotential k) lam) :
    0 ≤ lam := by
  let J := weightedDiskAmbientEmbedding (zeroTraceDomain Set.univ)
  have hJu : J u ≠ 0 := by
    intro h
    exact hne ((weightedDiskAmbientEmbedding_spec _).1 (h.trans (map_zero J).symm))
  have hn : 0 < ‖J u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hJu)
  have h := congrArg Complex.re ((mem_diskWeakEigenspace_all _ _ _ u).mp hu u)
  have hp := fullDirichlet_form_nonnegative hk u u.property
  have hi : (inner ℂ (J u) (J u)).re = ‖J u‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (J u)).symm
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  change (weakJacobi (surfacePotential k) u u).re = lam * (inner ℂ (J u) (J u)).re at h
  rw [hi] at h
  exact (mul_nonneg_iff_of_pos_right hn).mp (h ▸ hp)


/-- Zero is the least actual weak Dirichlet eigenvalue with spherical bulk mass. -/
theorem fullDirichlet_zero_isLeast_eigenvalue {k : ℕ} (hk : 3 ≤ k) :
    IsLeast {lam : ℝ | ∃ u : zeroTraceDomain Set.univ, u ≠ 0 ∧
      u ∈ diskWeakEigenspace (zeroTraceDomain Set.univ) (surfacePotential k) lam} 0 := by
  constructor
  · refine ⟨fullVerticalVector (by omega : 2 ≤ k), ?_, ?_⟩
    · intro h
      exact radialDirichletH1_ne_zero (by omega : 2 ≤ k) (congrArg Subtype.val h)
    · apply (mem_diskWeakEigenspace_all _ _ _ _).mpr
      intro v
      simpa only [fullVerticalVector, Complex.ofReal_zero, zero_mul] using
        radialDirichletH1_weak (by omega : 2 ≤ k) v.val v.property
  · rintro lam ⟨u, hne, hu⟩
    exact fullDirichlet_eigenvalue_nonnegative hk lam u hne hu

end KsIndex.Spectral
