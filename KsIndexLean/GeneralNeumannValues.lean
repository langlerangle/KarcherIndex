module

public import KsIndexLean.GeneralNeumannClasses
public import KsIndexLean.JacobiWeakCharacters
public import KsIndexLean.ComplexH1ConjugationForm

@[expose] public section


/-!
# Horizontal witnesses for the general Neumann nullity table

The actual horizontal Jacobi field and its complex conjugate supply the
nonzero elements in rotation classes 1 and k-1. All kernels here are weak
form radicals on the disk; classical half-period transport is separate.
-/
noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.FormIndex

lemma conj_zeta_eq_pow_pred (k : ℕ) (hk : 0 < k) :
    (starRingEnd ℂ) (zeta k) = zeta k ^ (k - 1) := by
  have h := congrArg (starRingEnd ℂ) (xi_pow_pred k hk)
  simpa [xi] using h.symm

lemma horizontal_conj_character (k : ℕ) (hk : 2 ≤ k) :
    conjH1 (horizontalH1 k hk) ∈
      weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ (k - 1)) := by
  have h := conjH1_mem_weakCharacter _ _ (horizontalH1_character_one k hk)
  simpa only [pow_one, conj_zeta_eq_pow_pred k (by omega)] using h

lemma horizontal_conj_weak_neumann (k : ℕ) (hk : 2 ≤ k) (v : ComplexH1) :
    weakJacobi (surfacePotential k) (conjH1 (horizontalH1 k hk)) v = 0 := by
  have h := weakJacobi_conjH1 (surfacePotential k) (horizontalH1 k hk) (conjH1 v)
  rw [horizontal_weak_neumann, map_zero] at h
  simpa only [conjH1_apply, conjMap_involutive v] using h

lemma nn_nullity_pos_of_witness (k j : ℕ) (u : ComplexH1)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hne : u ≠ 0) (hQ : ∀ v, weakJacobi (surfacePotential k) u v = 0) :
    1 ≤ diskWeakNullity (mixedCharacterDomain k j true true) (surfacePotential k) := by
  let D := mixedCharacterDomain k j true true
  letI := diskDomain_innerProductSpace D
  letI : CompleteSpace D := (isClosed_mixedCharacterDomain k j true true).completeSpace_coe
  let R := formRadical (domainJacobiForm D (surfacePotential k))
  letI : FiniteDimensional ℂ R := diskRadical_finiteDimensional D (surfacePotential k)
  have huD : u ∈ D := ⟨by rw [mixedTraceDomain_NN]; exact Submodule.mem_top, hu⟩
  have huR : (⟨u, huD⟩ : D) ∈ R := by
    rw [mem_formRadical]
    intro v
    exact hQ v
  let x : R := ⟨⟨u, huD⟩, huR⟩
  have hx : x ≠ 0 := by
    intro h
    exact hne (congrArg (fun y : R => (y.val : ComplexH1)) h)
  letI : Nontrivial R := ⟨⟨x, 0, hx⟩⟩
  exact Module.finrank_pos (R := ℂ) (M := R)

lemma neumann_class_one_nullity_pos (k : ℕ) (hk : 2 ≤ k) :
    1 ≤ diskWeakNullity (mixedCharacterDomain k 1 true true) (surfacePotential k) :=
  nn_nullity_pos_of_witness k 1 _ (horizontalH1_character_one k hk)
    (horizontalH1_ne_zero k hk) (horizontal_weak_neumann k hk)

lemma neumann_class_pred_nullity_pos (k : ℕ) (hk : 2 ≤ k) :
    1 ≤ diskWeakNullity (mixedCharacterDomain k (k - 1) true true) (surfacePotential k) := by
  apply nn_nullity_pos_of_witness k (k - 1) _ (horizontal_conj_character k hk) ?_
    (horizontal_conj_weak_neumann k hk)
  intro h
  exact horizontalH1_ne_zero k hk (conjH1.injective (h.trans (map_zero conjH1).symm))

/-- The weak Neumann nullity row for all rotation classes, k>=3. -/
theorem neumann_class_nullity (k : ℕ) (hk : 3 ≤ k) (j : Fin k) :
    diskWeakNullity (mixedCharacterDomain k j true true) (surfacePotential k) =
      if (j : ℕ) = 1 ∨ (j : ℕ) = k - 1 then 1 else 0 := by
  classical
  let a : Fin k := ⟨1, by omega⟩
  let b : Fin k := ⟨k - 1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    dsimp [a, b] at this
    omega
  let f : Fin k → ℕ := fun r =>
    diskWeakNullity (mixedCharacterDomain k r true true) (surfacePotential k)
  let g : Fin k → ℕ := fun r => (if r = a then 1 else 0) + (if r = b then 1 else 0)
  have hfa : 1 ≤ f a := neumann_class_one_nullity_pos k (by omega)
  have hfb : 1 ≤ f b := neumann_class_pred_nullity_pos k (by omega)
  have hle : ∀ r ∈ (Finset.univ : Finset (Fin k)), g r ≤ f r := by
    intro r _
    by_cases ha : r = a
    · subst r
      simpa [g, hab] using hfa
    · by_cases hb : r = b
      · subst r
        simpa [g, ha] using hfb
      · simp [g, ha, hb]
  have hgs : ∑ r, g r = 2 := by simp [g, Finset.sum_add_distrib]
  have heq : ∑ r, g r = ∑ r, f r := by
    apply le_antisymm (Finset.sum_le_sum hle)
    rw [hgs]
    exact neumann_classes_nullity_sum_le_two hk
  have hj := ((Finset.sum_eq_sum_iff_of_le hle).mp heq j (Finset.mem_univ j)).symm
  change f j = _
  rw [hj]
  have hja : j = a ↔ (j : ℕ) = 1 := Fin.ext_iff
  have hjb : j = b ↔ (j : ℕ) = k - 1 := Fin.ext_iff
  dsimp [g]
  simp only [hja, hjb]
  split_ifs <;> omega

/-- The sum of all weak Neumann character nullities is exactly two. -/
theorem neumann_classes_nullity_sum (k : ℕ) (hk : 3 ≤ k) :
    (∑ r : Fin k, diskWeakNullity (mixedCharacterDomain k r true true)
      (surfacePotential k)) = 2 := by
  classical
  have hab : (1 : ℕ) ≠ k - 1 := by omega
  have hrow (r : Fin k) :
      diskWeakNullity (mixedCharacterDomain k r true true) (surfacePotential k) =
        (if r = (⟨1, by omega⟩ : Fin k) then 1 else 0) +
        (if r = (⟨k - 1, by omega⟩ : Fin k) then 1 else 0) := by
    rw [neumann_class_nullity k hk]
    simp only [Fin.ext_iff]
    split_ifs <;> omega
  simp_rw [hrow]
  simp [Finset.sum_add_distrib]

end KsIndex.Spectral
