module

public import KsIndexLean.FiniteWeakIdentity

@[expose] public section


open Set MeasureTheory TopologicalSpace
open scoped Distributions

noncomputable section
namespace KsIndex.Trace

/-- Local weak identities globalize; local integrability is retained explicitly. -/
theorem weakLine_of_local {Ω : Opens ℂ} {u g : ℂ → ℂ} (d : ℂ)
    (hu : LocallyIntegrableOn u Ω volume) (hg : LocallyIntegrableOn g Ω volume)
    (hlocal : ∀ z ∈ Ω, ∃ V : Opens ℂ, z ∈ V ∧
      TauCeti.HasWeakLineDerivOn volume V u g d) :
    TauCeti.HasWeakLineDerivOn volume Ω u g d := by
  classical
  choose U hU hweak using fun z : Ω => hlocal z z.property
  apply TauCeti.hasWeakLineDerivOn_iff_testFunction.mpr
  refine ⟨inferInstance, hu, hg, ?_⟩
  intro φ
  have hc : tsupport (φ : ℂ → ℝ) ⊆ ⋃ z : Ω, (U z : Set ℂ) := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, φ.tsupport_subset hz⟩, hU _⟩
  obtain ⟨s, hs⟩ := φ.hasCompactSupport.elim_finite_subcover
    (fun z : Ω => (U z : Set ℂ)) (fun z => (U z).isOpen) hc
  have hs' : tsupport (φ : ℂ → ℝ) ⊆ ⋃ z : s, (U z.val : Set ℂ) := by
    intro z hz
    obtain ⟨i, hi, hzU⟩ := mem_iUnion₂.mp (hs hz)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hzU⟩
  exact weak_identity_of_finite_cover (fun z : s => U z.val) d
    (fun z => hweak z.val) φ hs'

/-- Directionwise globalization yields a genuine weak Fréchet derivative. -/
theorem weakF_of_local {Ω : Opens ℂ} {u : ℂ → ℂ} {J : ℂ → ℂ →L[ℝ] ℂ}
    (hu : LocallyIntegrableOn u Ω volume)
    (hJ : ∀ d, LocallyIntegrableOn (fun z => J z d) Ω volume)
    (hlocal : ∀ z ∈ Ω, ∃ V : Opens ℂ, z ∈ V ∧
      TauCeti.HasWeakFDerivOn volume V u J) :
    TauCeti.HasWeakFDerivOn volume Ω u J := by
  apply TauCeti.hasWeakFDerivOn_iff.mpr
  intro d
  apply weakLine_of_local d hu (hJ d)
  intro z hz
  obtain ⟨V, hzV, hV⟩ := hlocal z hz
  exact ⟨V, hzV, hV.hasWeakLineDerivOn d⟩

end KsIndex.Trace
