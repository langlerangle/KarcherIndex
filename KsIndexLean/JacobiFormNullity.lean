module

public import KsIndexLean.FormNullityRadical
public import KsIndexLean.JacobiRadicalCounts

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical KsIndex.FormIndex

/-- A full coefficient-domain identification preserving the weak pairing
transports disk nullity to the spectral radical. The identification and pairing
identity are explicit obligations for each paper-facing consumer. -/
lemma disk_formNullity_eq_radical {κ : Type*}
    (B : (κ → ℂ) → (κ → ℂ) → ℂ) (C : Submodule ℂ (κ → ℂ))
    (D : Submodule ℂ ComplexH1) [CompleteSpace D] (V : BoundedRealPotential)
    (e : D ≃ₗ[ℂ] C)
    (hQ : ∀ u v, B (e u) (e v) = domainJacobiForm D V u v) :
    formNullity B C = (Module.finrank ℂ
      (@formRadical D inferInstance (diskDomain_innerProductSpace D) (domainJacobiForm D V)) : ℕ∞) := by
  let := diskRadical_finiteDimensional D V
  exact @formNullity_eq_spectral_radical κ D inferInstance (diskDomain_innerProductSpace D)
    B C e (domainJacobiForm D V) inferInstance hQ

lemma disk_formNullity_eq_infinite_count {κ : Type*}
    (B : (κ → ℂ) → (κ → ℂ) → ℂ) (C : Submodule ℂ (κ → ℂ))
    (D : Submodule ℂ ComplexH1) [CompleteSpace D] (V : BoundedRealPotential)
    [Infinite (diskSpectralData D V).eigenbasisIndex]
    (e : D ≃ₗ[ℂ] C)
    (hQ : ∀ u v, B (e u) (e v) = domainJacobiForm D V u v) :
    formNullity B C = ((diskNonpositiveCount D V - diskNegativeCount D V : ℕ) : ℕ∞) := by
  rw [disk_formNullity_eq_radical B C D V e hQ, diskRadical_finrank_eq_count]

lemma disk_formNullity_eq_finite_count {κ : Type*}
    (B : (κ → ℂ) → (κ → ℂ) → ℂ) (C : Submodule ℂ (κ → ℂ))
    (D : Submodule ℂ ComplexH1) [CompleteSpace D] (V : BoundedRealPotential)
    [FiniteDimensional ℂ (WeightedDiskAmbient D)]
    (e : D ≃ₗ[ℂ] C)
    (hQ : ∀ u v, B (e u) (e v) = domainJacobiForm D V u v) :
    formNullity B C = (((diskSpectralData D V).finiteWeakCount (V.C + 1) 0 -
      (diskSpectralData D V).finiteStrictCount (V.C + 1) 0 : ℕ) : ℕ∞) := by
  rw [disk_formNullity_eq_radical B C D V e hQ, diskRadical_finrank_eq_finite_count]

lemma finiteCopy_formNullity_eq_radical {κ ι : Type*} [Fintype ι]
    (B : (κ → ℂ) → (κ → ℂ) → ℂ) (C : Submodule ℂ (κ → ℂ))
    (D : Submodule ℂ (ι → ComplexH1)) [CompleteSpace (finiteH1Domain D)]
    (V : BoundedRealPotential) (e : finiteH1Domain D ≃ₗ[ℂ] C)
    (hQ : ∀ u v, B (e u) (e v) = finiteJacobiForm D V u v) :
    formNullity B C = (Module.finrank ℂ
      (@formRadical (finiteH1Domain D) inferInstance (finiteH1Domain_innerProductSpace D)
        (finiteJacobiForm D V)) : ℕ∞) := by
  let := finiteCopyRadical_finiteDimensional D V
  exact @formNullity_eq_spectral_radical κ (finiteH1Domain D) inferInstance
    (finiteH1Domain_innerProductSpace D) B C e (finiteJacobiForm D V) inferInstance hQ

end KsIndex.Spectral
