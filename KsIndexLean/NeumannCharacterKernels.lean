module

public import KsIndexLean.NeumannKernelClassification
public import KsIndexLean.PaperCharacterTestExtension

@[expose] public section


noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.FormIndex KsIndex.Spectral

lemma paperCharacter_trace_coeff_zero (j : ℕ) (u : ComplexH1)
    (hu : u ∈ paperHemisphereCharacter j) (n : ℤ)
    (hn : ¬ ∃ m : ℤ, n = -(j : ℤ) + 3 * m) :
    circleFourierCoeff (diskTraceCLM u) n = 0 := by
  apply (boundaryRotation_eigen_iff_support 3 (by decide) (j : ℤ) (diskTraceCLM u)).mp
  · simpa only [zpow_natCast, Nat.cast_ofNat] using trace_character hu
  · exact hn

lemma paperHemisphere_kernel_full (j : ℕ) (u : paperHemisphereCharacter j)
    (hu : ∀ v : paperHemisphereCharacter j, weakJacobi (surfacePotential 3) u v = 0) :
    ∀ v : ComplexH1, weakJacobi (surfacePotential 3) u v = 0 :=
  paperNeumann_character_tests_extend j u u.property (fun v hv => hu ⟨v, hv⟩)

lemma paperHemisphere_zero_kernel (u : paperHemisphereCharacter 0)
    (hu : ∀ v : paperHemisphereCharacter 0, weakJacobi (surfacePotential 3) u v = 0) :
    (u : ComplexH1) = 0 := by
  have h := weak_neumann_eq_horizontal_combination u (paperHemisphere_kernel_full 0 u hu)
  rw [paperCharacter_trace_coeff_zero 0 u u.property 2 (by rintro ⟨m, hm⟩; omega),
    paperCharacter_trace_coeff_zero 0 u u.property (-2) (by rintro ⟨m, hm⟩; omega)] at h
  simpa only [zero_smul, add_zero] using h

lemma paperHemisphere_one_kernel_iff (u : paperHemisphereCharacter 1) :
    (∀ v : paperHemisphereCharacter 1, weakJacobi (surfacePotential 3) u v = 0) ↔
      ∃ c : ℂ, (u : ComplexH1) = c • horizontalThreeH1 := by
  constructor
  · intro hu
    have h := weak_neumann_eq_horizontal_combination u (paperHemisphere_kernel_full 1 u hu)
    rw [paperCharacter_trace_coeff_zero 1 u u.property (-2) (by rintro ⟨m, hm⟩; omega),
      zero_smul, add_zero] at h
    exact ⟨_, h⟩
  · rintro ⟨c, hc⟩ v
    rw [hc, weakJacobi_smul_left, horizontalThree_weak_neumann, mul_zero]

lemma paperHemisphere_two_kernel_iff (u : paperHemisphereCharacter 2) :
    (∀ v : paperHemisphereCharacter 2, weakJacobi (surfacePotential 3) u v = 0) ↔
      ∃ c : ℂ, (u : ComplexH1) = c • horizontalThreeConjH1 := by
  constructor
  · intro hu
    have h := weak_neumann_eq_horizontal_combination u (paperHemisphere_kernel_full 2 u hu)
    rw [paperCharacter_trace_coeff_zero 2 u u.property 2 (by rintro ⟨m, hm⟩; omega),
      zero_smul, zero_add] at h
    exact ⟨_, h⟩
  · rintro ⟨c, hc⟩ v
    rw [hc, weakJacobi_smul_left, horizontalThreeConj_weak_neumann, mul_zero]

end KsIndex.Trace

namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical
local instance hemisphereInner (j : ℕ) : InnerProductSpace ℂ (paperHemisphereCharacter j) :=
  diskDomain_innerProductSpace (paperHemisphereCharacter j)

def horizontalCharacterOne : paperHemisphereCharacter 1 :=
  ⟨horizontalThreeH1, horizontalThreeH1_character_one⟩
def horizontalCharacterTwo : paperHemisphereCharacter 2 :=
  ⟨horizontalThreeConjH1, horizontalThreeConjH1_character_two⟩

lemma paperHemisphere_zero_radical :
    formRadical (domainJacobiForm (paperHemisphereCharacter 0) (surfacePotential 3)) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro u hu
  change u = 0
  apply Subtype.ext
  exact paperHemisphere_zero_kernel u (fun v => (mem_formRadical _ u).mp hu v)

lemma paperHemisphere_one_radical :
    formRadical (domainJacobiForm (paperHemisphereCharacter 1) (surfacePotential 3)) =
      Submodule.span ℂ {horizontalCharacterOne} := by
  ext u
  rw [mem_formRadical, Submodule.mem_span_singleton]
  simp only [domainJacobiForm_apply]
  rw [paperHemisphere_one_kernel_iff]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, Subtype.ext hc.symm⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩

lemma paperHemisphere_two_radical :
    formRadical (domainJacobiForm (paperHemisphereCharacter 2) (surfacePotential 3)) =
      Submodule.span ℂ {horizontalCharacterTwo} := by
  ext u
  rw [mem_formRadical, Submodule.mem_span_singleton]
  simp only [domainJacobiForm_apply]
  rw [paperHemisphere_two_kernel_iff]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, Subtype.ext hc.symm⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩

lemma paperHemisphere_zero_nullity : diskWeakNullity (paperHemisphereCharacter 0) (surfacePotential 3) = 0 := by
  unfold diskWeakNullity
  rw [paperHemisphere_zero_radical]
  exact finrank_bot ℂ _

lemma paperHemisphere_one_nullity : diskWeakNullity (paperHemisphereCharacter 1) (surfacePotential 3) = 1 := by
  unfold diskWeakNullity
  rw [paperHemisphere_one_radical]
  apply finrank_span_singleton
  intro h
  exact horizontalThreeH1_ne_zero (congrArg Subtype.val h)

lemma paperHemisphere_two_nullity : diskWeakNullity (paperHemisphereCharacter 2) (surfacePotential 3) = 1 := by
  unfold diskWeakNullity
  rw [paperHemisphere_two_radical]
  apply finrank_span_singleton
  intro h
  exact horizontalThreeConjH1_ne_zero (congrArg Subtype.val h)

end KsIndex.Spectral
