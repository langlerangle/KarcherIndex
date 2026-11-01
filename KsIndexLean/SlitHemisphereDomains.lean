module

public import KsIndexLean.SlitReflectionNullity

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1

/-- Flags are ordered (arc1, arc0); true means natural Neumann. -/
lemma paperHemisphereCharacter_eq_NN (j : ℕ) :
    paperHemisphereCharacter j = mixedCharacterDomain 3 j true true := by
  simp [mixedCharacterDomain, mixedTraceDomain, naturalArcDomain]

lemma paperNeumannOddCharacter_eq_DN (j : ℕ) :
    paperNeumannOddCharacter j = mixedCharacterDomain 3 j false true := by
  simp [paperNeumannOddCharacter, mixedCharacterDomain, mixedTraceDomain, naturalArcDomain]

lemma paperDirichletEvenCharacter_eq_ND (j : ℕ) :
    paperDirichletEvenCharacter j = mixedCharacterDomain 3 j true false := by
  simp [paperDirichletEvenCharacter, mixedCharacterDomain, mixedTraceDomain, naturalArcDomain]

lemma paperDirichletOddCharacter_eq_DD (j : ℕ) :
    paperDirichletOddCharacter j = mixedCharacterDomain 3 j false false := by
  simp only [paperDirichletOddCharacter, paperDirichletEvenCharacter,
    mixedCharacterDomain, mixedTraceDomain, naturalArcDomain, Bool.false_eq_true,
    ↓reduceIte, paperHemisphereCharacter, Nat.cast_ofNat, inf_assoc]

/-- Actual weak nullities in the repository's named mixed boundary spaces.
No identification of the two opposite mixed problems is assumed. -/
lemma paperSlitNeumannCharacter_nullity_mixed (j : ℕ) (V : BoundedRealPotential) :
    finiteCopyWeakNullity (pairFiniteDomain (paperSlitNeumannCharacterDomain j)) V =
      diskWeakNullity (mixedCharacterDomain 3 j true true) V +
      diskWeakNullity (mixedCharacterDomain 3 j false true) V := by
  simpa only [paperHemisphereCharacter_eq_NN, paperNeumannOddCharacter_eq_DN] using
    paperSlitNeumannCharacter_nullity j V

lemma paperSlitDirichletCharacter_nullity_mixed (j : ℕ) (V : BoundedRealPotential) :
    finiteCopyWeakNullity (pairFiniteDomain (paperSlitDirichletCharacterDomain j)) V =
      diskWeakNullity (mixedCharacterDomain 3 j true false) V +
      diskWeakNullity (mixedCharacterDomain 3 j false false) V := by
  simpa only [paperDirichletEvenCharacter_eq_ND, paperDirichletOddCharacter_eq_DD] using
    paperSlitDirichletCharacter_nullity j V

end KsIndex.Spectral
