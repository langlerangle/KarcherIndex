module

public import KsIndexLean.NeumannCharacterKernels
public import KsIndexLean.DirichletCharacterKernels

@[expose] public section


/-!
# Pure-sector nullity values (k = 3), in the `mixedCharacterDomain` spelling

The domain identities below identify `mixedCharacterDomain 3 j` with the
pure Dirichlet and Neumann character spaces, then transfer their nullity values.
For `j < 3`, Dirichlet nullity is one only at `j = 0`; Neumann nullity is one
at `j = 1, 2` and zero at `j = 0`.

The pure Dirichlet flags are `(false, false)`, imposing zero trace on both arcs.
The pure Neumann flags are `(true, true)`, imposing no trace restriction.
-/

noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical KsIndex.Trace

/-! ### Spelling bridges -/

/-- The `(true,true)` sector is the pure Neumann character sector. -/
lemma mixedCharacterDomain_NN_eq (j : ℕ) :
    mixedCharacterDomain 3 j true true = paperHemisphereCharacter j := by
  simp only [mixedCharacterDomain, mixedTraceDomain_NN, top_inf_eq, paperHemisphereCharacter,
    Nat.cast_ofNat]

/-- The `(false,false)` sector is the pure (odd) Dirichlet character sector. -/
lemma mixedCharacterDomain_DD_eq (j : ℕ) :
    mixedCharacterDomain 3 j false false = paperDirichletOddCharacter j := by
  simp only [mixedCharacterDomain, mixedTraceDomain, naturalArcDomain, paperDirichletOddCharacter,
    paperDirichletEvenCharacter, paperHemisphereCharacter, Bool.false_eq_true, ite_false,
    Nat.cast_ofNat, inf_assoc]

/-! ### The pure-sector values -/

/-- **Dirichlet (DD) sector nullity, k=3**: `δ_{j,0}` — the vertical field at `r=0`. -/
lemma pureSector_dirichlet_nullity (j : ℕ) (hj : j < 3) :
    diskWeakNullity (mixedCharacterDomain 3 j false false) (surfacePotential 3)
      = if j = 0 then 1 else 0 := by
  rw [mixedCharacterDomain_DD_eq]
  rcases eq_or_ne j 0 with h | h
  · subst h; simpa using paperDirichletOddCharacter_zero_nullity
  · simpa [h] using paperDirichletOddCharacter_nontrivial_nullity j (by omega)

/-- **Neumann (NN) sector nullity, k=3**: `[j ≡ ±1]` — the two horizontal fields at `r=1,2`. -/
lemma pureSector_neumann_nullity (j : ℕ) (hj : j < 3) :
    diskWeakNullity (mixedCharacterDomain 3 j true true) (surfacePotential 3)
      = if j = 0 then 0 else 1 := by
  rw [mixedCharacterDomain_NN_eq]
  interval_cases j
  · simpa using paperHemisphere_zero_nullity
  · simpa using paperHemisphere_one_nullity
  · simpa using paperHemisphere_two_nullity

end KsIndex.Spectral
