module

public import KsIndexLean.GroundStateDirichlet
public import KsIndexLean.MixedDirichletDomainIdentity
public import KsIndexLean.SlitReflectionIndex

@[expose] public section


/-! # Ground-state (geometric) index-zero for the pure Dirichlet character block

Geometric replacement for `WeakHemisphereIndex.pureDirichlet_weak_index_zero`
(which routes through the Fourier `seamNat_pureD`): the negative index of the weak
Jacobi form on the pure-Dirichlet character block is zero, because the form is
nonnegative there by the positive-vertical-ground-state nonnegativity
`GroundState.fullDirichlet_nonnegative_ground_state`. Bridge-independent.
-/
noncomputable section
open Set MeasureTheory
namespace KsIndex.GroundState
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spectral KsIndex.FormIndex KsIndex.NegativeDensity

/-- The weak Jacobi form is nonnegative on the pure-Dirichlet character block,
since that block lies in the full zero-trace domain. -/
lemma mixedDD_weakJacobi_nonneg {k : ℕ} (hk : 2 ≤ k) (r : ℕ)
    (u : mixedCharacterDomain k r false false) :
    0 ≤ (weakJacobi (surfacePotential k) (u : ComplexH1) (u : ComplexH1)).re := by
  have hmem : (u : ComplexH1) ∈ zeroTraceDomain Set.univ := by
    have hu : (u : ComplexH1) ∈ zeroTraceDomain Set.univ ⊓
        weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ r) := by
      rw [← mixedDD_eq_fullDirichletCharacter (by omega) r]
      exact u.property
    exact (Submodule.mem_inf.mp hu).1
  exact fullDirichlet_nonnegative_ground_state hk (u : ComplexH1) hmem

/-- **Geometric pure-Dirichlet index zero**, `k ≥ 3`: no Fourier `seamNat_pureD`. -/
theorem pureDirichlet_weak_index_zero_ground_state {k : ℕ} (hk : 3 ≤ k) (r : ℕ) :
    diskWeakIndex (mixedCharacterDomain k r false false) (surfacePotential k) = 0 := by
  unfold diskWeakIndex negativeIndex
  apply le_antisymm _ zero_le
  refine iSup_le fun V => iSup_le fun hVneg => iSup_le fun _hVfin => ?_
  have hVbot : V = ⊥ := by
    rw [eq_bot_iff]
    intro x hxV
    rw [Submodule.mem_bot]
    by_contra hx0
    exact absurd (mixedDD_weakJacobi_nonneg (by omega) r x) (not_le.mpr (hVneg x hxV hx0))
  rw [hVbot, finrank_bot]
  simp

end KsIndex.GroundState
