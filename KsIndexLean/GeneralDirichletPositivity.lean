module

public import KsIndexLean.GeneralDirichletKernel
public import KsIndexLean.IndexZeroPositivity
public import KsIndexLean.WeakHemisphereIndex
public import KsIndexLean.MixedDirichletDomainIdentity
public import KsIndexLean.GroundStateDirichletIndexZero

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.FormIndex

/-- The paper's nontrivial zero-trace character block is positive definite on
its full weak domain, not merely on a smooth core. -/
lemma generalDirichlet_character_positive {k : ℕ} (hk : 3 ≤ k) (j : ℕ)
    (hj : zeta k ^ j ≠ 1) (u : mixedCharacterDomain k j false false) (hu : u ≠ 0) :
    0 < (weakJacobi (surfacePotential k) u u).re := by
  apply form_positive_of_index_zero_kernel_zero
    (domainJacobiForm (mixedCharacterDomain k j false false) (surfacePotential k))
    (fun x y => weakJacobi_conj _ x y)
    (KsIndex.GroundState.pureDirichlet_weak_index_zero_ground_state hk j) ?_ u hu
  intro v hv
  apply Subtype.ext
  apply generalDirichlet_character_kernel_zero (by omega) j hj v
  · rw [← mixedDD_eq_fullDirichletCharacter (by omega) j]
    exact v.property
  · intro w hw
    have hm : w ∈ mixedCharacterDomain k j false false := by
      rw [mixedDD_eq_fullDirichletCharacter (by omega) j]
      exact hw
    exact hv ⟨w, hm⟩

lemma generalDirichlet_character_positive_of_range {k j : ℕ}
    (hk : 3 ≤ k) (hj0 : 0 < j) (hjk : j < k)
    (u : mixedCharacterDomain k j false false) (hu : u ≠ 0) :
    0 < (weakJacobi (surfacePotential k) u u).re := by
  apply generalDirichlet_character_positive hk j ?_ u hu
  intro he
  have hd := ((zeta_prim (by omega : 0 < k)).pow_eq_one_iff_dvd j).mp he
  exact (not_le_of_gt hjk) (Nat.le_of_dvd hj0 hd)

end KsIndex.Spectral
