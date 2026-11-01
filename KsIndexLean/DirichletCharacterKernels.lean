module

public import KsIndexLean.PaperCharacterTestExtension

@[expose] public section


noncomputable section
open Set
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.FormIndex

abbrev fullDirichletCharacter (j : ℕ) : Submodule ℂ ComplexH1 :=
  zeroTraceDomain Set.univ ⊓ weakCharacterDomain (-(2 * Real.pi) / 3) (zeta 3 ^ j)

lemma fullDirichletCharacter_kernel_zero_of_nontrivial (j : ℕ) (hj : zeta 3 ^ j ≠ 1)
    (u : fullDirichletCharacter j)
    (hQ : ∀ v : fullDirichletCharacter j, weakJacobi (surfacePotential 3) u v = 0) :
    (u : ComplexH1) = 0 := by
  obtain ⟨c, hc⟩ := paperDirichlet_character_kernel_spanned j u u.property
    (fun v hv => hQ ⟨v, hv⟩)
  have hv := (mem_weakCharacterDomain _ _ verticalThreeH1).mp verticalThreeH1_character_zero
  simp only [pow_zero, one_smul] at hv
  have hrot : diskRotation (-(2 * Real.pi) / 3) (u : ComplexH1) = u := by
    rw [hc, map_smul, hv]
  have he := (mem_weakCharacterDomain _ _ (u : ComplexH1)).mp u.property.2
  rw [hrot] at he
  have hz : (1 - zeta 3 ^ j) • (u : ComplexH1) = 0 := by
    rw [sub_smul, one_smul, ← he, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (Ne.symm hj))

lemma fullDirichletCharacter_kernel_zero_of_not_dvd (j : ℕ) (hj : ¬ 3 ∣ j)
    (u : fullDirichletCharacter j)
    (hQ : ∀ v : fullDirichletCharacter j, weakJacobi (surfacePotential 3) u v = 0) :
    (u : ComplexH1) = 0 :=
  fullDirichletCharacter_kernel_zero_of_nontrivial j
    (fun h => hj (((zeta_prim (by decide : 0 < 3)).pow_eq_one_iff_dvd j).mp h)) u hQ

lemma fullDirichletCharacter_zero_kernel_iff (u : fullDirichletCharacter 0) :
    (∀ v : fullDirichletCharacter 0, weakJacobi (surfacePotential 3) u v = 0) ↔
      ∃ c : ℂ, (u : ComplexH1) = c • verticalThreeH1 := by
  constructor
  · intro hQ
    exact paperDirichlet_character_kernel_spanned 0 u u.property (fun v hv => hQ ⟨v, hv⟩)
  · rintro ⟨c, hc⟩ v
    rw [hc, weakJacobi_smul_left, verticalThree_dirichlet_weak ⟨v, v.property.1⟩, mul_zero]

end KsIndex.Trace

namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

local instance characterDirichletInner (j : ℕ) : InnerProductSpace ℂ (fullDirichletCharacter j) :=
  diskDomain_innerProductSpace (fullDirichletCharacter j)

def verticalDirichletCharacterVector : fullDirichletCharacter 0 :=
  ⟨verticalThreeH1, verticalThreeH1_zeroTrace _, verticalThreeH1_character_zero⟩

lemma fullDirichletCharacter_radical_zero (j : ℕ) (hj : ¬ 3 ∣ j) :
    formRadical (domainJacobiForm (fullDirichletCharacter j) (surfacePotential 3)) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro u hu
  change u = 0
  apply Subtype.ext
  exact fullDirichletCharacter_kernel_zero_of_not_dvd j hj u
    (fun v => (mem_formRadical _ u).mp hu v)

lemma fullDirichletCharacter_zero_radical_span :
    formRadical (domainJacobiForm (fullDirichletCharacter 0) (surfacePotential 3)) =
      Submodule.span ℂ {verticalDirichletCharacterVector} := by
  ext u
  rw [mem_formRadical, Submodule.mem_span_singleton]
  simp only [domainJacobiForm_apply]
  rw [fullDirichletCharacter_zero_kernel_iff]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, Subtype.ext hc.symm⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩

lemma fullDirichletCharacter_zero_nullity :
    diskWeakNullity (fullDirichletCharacter 0) (surfacePotential 3) = 1 := by
  unfold diskWeakNullity
  rw [fullDirichletCharacter_zero_radical_span]
  apply finrank_span_singleton
  intro h
  exact verticalThreeH1_ne_zero (congrArg Subtype.val h)

lemma fullDirichletCharacter_nontrivial_nullity (j : ℕ) (hj : ¬ 3 ∣ j) :
    diskWeakNullity (fullDirichletCharacter j) (surfacePotential 3) = 0 := by
  unfold diskWeakNullity
  rw [fullDirichletCharacter_radical_zero j hj]
  exact finrank_bot ℂ (fullDirichletCharacter j)

/-- The odd Dirichlet reflection component has full zero boundary trace. -/
lemma paperDirichletOddCharacter_eq_full (j : ℕ) :
    paperDirichletOddCharacter j = fullDirichletCharacter j := by
  ext u
  change (u ∈ zeroTraceDomain (boundaryArc 3 1) ∧
    u ∈ zeroTraceDomain (boundaryArc 3 0) ∧ u ∈ paperHemisphereCharacter j) ↔
    (u ∈ zeroTraceDomain Set.univ ∧ u ∈ paperHemisphereCharacter j)
  have he := full_trace_eq_iff_arcs (by decide : 1 ≤ 3) u (0 : ComplexH1)
  simp only [map_zero] at he
  change (arcTrace (boundaryArc 3 1) u = 0 ∧
    arcTrace (boundaryArc 3 0) u = 0 ∧ u ∈ paperHemisphereCharacter j) ↔
    (arcTrace Set.univ u = 0 ∧ u ∈ paperHemisphereCharacter j)
  rw [he]
  tauto

lemma paperDirichletOddCharacter_zero_nullity :
    diskWeakNullity (paperDirichletOddCharacter 0) (surfacePotential 3) = 1 := by
  rw [paperDirichletOddCharacter_eq_full]
  exact fullDirichletCharacter_zero_nullity

lemma paperDirichletOddCharacter_nontrivial_nullity (j : ℕ) (hj : ¬ 3 ∣ j) :
    diskWeakNullity (paperDirichletOddCharacter j) (surfacePotential 3) = 0 := by
  rw [paperDirichletOddCharacter_eq_full]
  exact fullDirichletCharacter_nontrivial_nullity j hj

end KsIndex.Spectral
