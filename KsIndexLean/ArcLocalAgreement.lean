module

public import KsIndexLean.LocalBoundaryAgreement

@[expose] public section


open Set MeasureTheory

namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Locally proved a.e. identities patch over any subset of the second-countable circle. -/
lemma ae_on_of_local_neighbourhoods {A : Set Circle₁} {P : Circle₁ → Prop}
    (h : ∀ x ∈ A, ∃ U : Set Circle₁, IsOpen U ∧ x ∈ U ∧ ∀ᵐ w ∂circleMeasure.restrict U, P w) :
    ∀ᵐ w ∂circleMeasure.restrict A, P w := by
  classical
  choose U hU hx hP using fun x : A => h x x.property
  have hcover : A ⊆ ⋃ x : A, U x := by
    intro x hxA
    exact mem_iUnion.mpr ⟨⟨x, hxA⟩, hx ⟨x, hxA⟩⟩
  obtain ⟨J, hJ, hJA⟩ := (HereditarilyLindelofSpace.isLindelof A).elim_countable_subcover
    U hU hcover
  have hall : ∀ᵐ w ∂circleMeasure.restrict (⋃ x ∈ J, U x), P w :=
    (ae_restrict_biUnion_iff U hJ P).mpr (fun x _ => hP x)
  exact hall.filter_mono (ae_mono (Measure.restrict_mono hJA le_rfl))

/-- Local continuous extensions along an arc determine the actual weak trace there. -/
theorem diskTrace_local_agreement (u : ComplexH1) {A : Set Circle₁} {f : ℂ → ℂ}
    (hlocal : ∀ x ∈ A, ∃ O : Set ℂ, IsOpen O ∧ (x : ℂ) ∈ O ∧ ContinuousOn f O ∧
      ∀ᵐ z ∂volume.restrict (disk : Set ℂ), z ∈ O → valueCLM u z = f z) :
    (diskTraceCLM u : Circle₁ → ℂ) =ᵐ[circleMeasure.restrict A] (fun w => f (w : ℂ)) := by
  apply ae_on_of_local_neighbourhoods
  intro x hx
  obtain ⟨O, hO, hxO, hf, he⟩ := hlocal x hx
  exact exists_boundary_neighbourhood_agreement u hO hf hxO he

/-- A single open extension region gives agreement on its whole boundary intersection. -/
theorem diskTrace_open_extension (u : ComplexH1) {O : Set ℂ} (hO : IsOpen O)
    {f : ℂ → ℂ} (hf : ContinuousOn f O)
    (he : ∀ᵐ z ∂volume.restrict (disk : Set ℂ), z ∈ O → valueCLM u z = f z) :
    (diskTraceCLM u : Circle₁ → ℂ) =ᵐ[circleMeasure.restrict {w : Circle₁ | (w : ℂ) ∈ O}]
      (fun w => f (w : ℂ)) :=
  diskTrace_local_agreement u (fun _ hx => ⟨O, hO, hx, hf, he⟩)

end KsIndex.Trace
