module

public import KsIndexLean.GeneralDirichletPositivity

@[expose] public section


/-!
# Pure Dirichlet sector nullities for general k

`nul(DD, j) = δ_{j,0}` for every `k ≥ 2` and `j < k`, expressed using
`mixedCharacterDomain`. The proof combines the kernel classification
`generalDirichlet_kernel_span`, the vanishing theorem for nontrivial characters
`generalDirichlet_character_kernel_zero`, and the radial witness
`radialDirichletH1` in the trivial character.
-/

noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.FormIndex

variable {k : ℕ}

local instance generalCharacterDirichletInner (k j : ℕ) :
    InnerProductSpace ℂ
      ↥(zeroTraceDomain Set.univ ⊓
        weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j)) :=
  diskDomain_innerProductSpace _

/-- The general vertical witness, packaged in the class-`0` full Dirichlet domain. -/
def generalVerticalVector (hk : 2 ≤ k) :
    ↥(zeroTraceDomain Set.univ ⊓
      weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ 0)) :=
  ⟨radialDirichletH1 hk,
    (mem_fullZeroTrace_iff _).mpr (radialDirichletH1_trace hk),
    (mem_weakCharacterDomain _ _ _).mpr (by
      rw [pow_zero, one_smul]
      exact radialDirichletH1_rotation hk _)⟩

/-- Nontrivial character: the domain-form radical is trivial. -/
lemma generalDirichletCharacter_radical_zero (hk : 2 ≤ k) (j : ℕ)
    (hj : zeta k ^ j ≠ 1) :
    formRadical (domainJacobiForm
      (zeroTraceDomain Set.univ ⊓
        weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
      (surfacePotential k)) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro u hu
  change u = 0
  apply Subtype.ext
  apply generalDirichlet_character_kernel_zero hk j hj u.val u.property
  intro w hw
  exact (mem_formRadical _ u).mp hu ⟨w, hw⟩

/-- Class `0`: the domain kernel is exactly the multiples of the radial witness. -/
lemma generalDirichlet_zero_kernel_iff (hk : 2 ≤ k)
    (u : ↥(zeroTraceDomain Set.univ ⊓
      weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ 0))) :
    (∀ v : ↥(zeroTraceDomain Set.univ ⊓
        weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ 0)),
      weakJacobi (surfacePotential k) u v = 0) ↔
      ∃ c : ℂ, (u : ComplexH1) = c • radialDirichletH1 hk := by
  constructor
  · intro hQ
    exact generalDirichlet_kernel_span hk u u.property.1
      (generalDirichlet_character_tests_extend (by omega) 0 u u.property.2
        (fun v hv => hQ ⟨v, hv⟩))
  · rintro ⟨c, hc⟩ v
    rw [hc, weakJacobi_smul_left,
      radialDirichletH1_weak hk v v.property.1, mul_zero]

set_option maxHeartbeats 800000 in
-- The `mem_formRadical`/`mem_span_singleton` rewrites unify the domain-form
-- instances on a symbolic-`k` subtype; default heartbeats time out at `isDefEq`.
lemma generalDirichlet_zero_radical_span (hk : 2 ≤ k) :
    formRadical (domainJacobiForm
      (zeroTraceDomain Set.univ ⊓
        weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ 0))
      (surfacePotential k)) =
      Submodule.span ℂ {generalVerticalVector hk} := by
  ext u
  rw [mem_formRadical, Submodule.mem_span_singleton]
  simp only [domainJacobiForm_apply]
  rw [generalDirichlet_zero_kernel_iff hk]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, Subtype.ext hc.symm⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩

lemma generalDirichlet_zero_nullity (hk : 2 ≤ k) :
    diskWeakNullity
      (zeroTraceDomain Set.univ ⊓
        weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ 0))
      (surfacePotential k) = 1 := by
  unfold diskWeakNullity
  rw [generalDirichlet_zero_radical_span hk]
  apply finrank_span_singleton
  intro h
  exact radialDirichletH1_ne_zero hk (congrArg Subtype.val h)

lemma generalDirichlet_nontrivial_nullity (hk : 2 ≤ k) (j : ℕ)
    (hj : zeta k ^ j ≠ 1) :
    diskWeakNullity
      (zeroTraceDomain Set.univ ⊓
        weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
      (surfacePotential k) = 0 := by
  unfold diskWeakNullity
  rw [generalDirichletCharacter_radical_zero hk j hj]
  exact finrank_bot ℂ _

/-- **V2 headline: `nul(DD, j) = δ_{j,0}` at every `k ≥ 2`**, in the
`mixedCharacterDomain` spelling the capstone sum consumes. -/
theorem pureSector_dirichlet_nullity_gen (hk : 2 ≤ k) {j : ℕ} (hjk : j < k) :
    diskWeakNullity (mixedCharacterDomain k j false false) (surfacePotential k)
      = if j = 0 then 1 else 0 := by
  rw [mixedDD_eq_fullDirichletCharacter (by omega) j]
  rcases eq_or_ne j 0 with h | h
  · subst h
    simpa using generalDirichlet_zero_nullity hk
  · have hz : zeta k ^ j ≠ 1 := by
      intro he
      have hd := ((zeta_prim (by omega : 0 < k)).pow_eq_one_iff_dvd j).mp he
      exact h (Nat.eq_zero_of_dvd_of_lt hd hjk)
    simpa [h] using generalDirichlet_nontrivial_nullity hk j hz

end KsIndex.Spectral
