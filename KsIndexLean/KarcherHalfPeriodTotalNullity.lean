module

public import KsIndexLean.KarcherHalfPeriodRadical
public import KsIndexLean.GeneralNeumannRow
public import KsIndexLean.GeneralNeumannValues
public import KsIndexLean.GeneralDirichletValues
public import KsIndexLean.ZeroPhaseReflectionIndex

@[expose] public section


/-! Unrestricted classical half-period fields map into the full weak kernel.
These carriers retain bounded classical fields, not compact-test radicals. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spectral
variable {k : ℕ} [h : Fact (2 ≤ k)]

abbrev halfPeriodFullWeakRadical (k : ℕ) (b : Bool) :=
  @formRadical (mixedTraceDomain k b b) inferInstance
    (diskDomain_innerProductSpace _)
    (domainJacobiForm (mixedTraceDomain k b b) (surfacePotential k))

/-- Forward weak realization without a rotation-character restriction. -/
def classicalHalfPeriodToFullRadical (R : PaperHalfPeriodRealization k) (b : Bool) :
    R.classicalHalfPeriodSpace b →ₗ[ℂ] halfPeriodFullWeakRadical k b := by
  let L : R.classicalHalfPeriodSpace b →ₗ[ℂ] mixedTraceDomain k b b :=
    (R.classicalHalfPeriodToH1 b).codRestrict _ (by
      intro u
      cases b
      · rw [← full_zeroTrace_eq (by have := h.out; omega : 1 ≤ k)]
        exact (R.classicalHalfPeriodData u).toDisk.dirichlet_mem_zeroTrace h.out
      · rw [mixedTraceDomain_NN]
        trivial)
  exact L.codRestrict _ (by
    intro u
    apply (mem_formRadical _ _).mpr
    intro v
    change weakJacobi (surfacePotential k) (R.classicalHalfPeriodToH1 b u) v.val = 0
    cases b
    · exact (R.classicalHalfPeriodData u).toDisk.dirichlet_tests_zero h.out v.val
        (by simpa only [← full_zeroTrace_eq (by have := h.out; omega : 1 ≤ k)] using v.property)
    · exact (R.classicalHalfPeriodData u).toDisk.neumann_tests_zero h.out v.val)

theorem classicalHalfPeriodToFullRadical_injective (R : PaperHalfPeriodRealization k)
    (b : Bool) : Function.Injective (R.classicalHalfPeriodToFullRadical b) := by
  intro u v he
  apply R.classicalHalfPeriodToH1_injective b
  exact congrArg (fun x : halfPeriodFullWeakRadical k b => x.val.val) he

/-- The actual unrestricted classical field space is finite dimensional. -/
theorem classicalHalfPeriodSpace_finiteDimensional (R : PaperHalfPeriodRealization k)
    (b : Bool) : FiniteDimensional ℂ (R.classicalHalfPeriodSpace b) := by
  let : FiniteDimensional ℂ (halfPeriodFullWeakRadical k b) :=
    diskRadical_finiteDimensional _ _
  exact FiniteDimensional.of_injective (R.classicalHalfPeriodToFullRadical b)
    (R.classicalHalfPeriodToFullRadical_injective b)

/-- The complex dimension of unrestricted bounded Neumann Jacobi fields is at most two. -/
theorem classicalHalfPeriodNeumann_finrank_le_two (R : PaperHalfPeriodRealization k)
    (hk : 3 ≤ k) : Module.finrank ℂ (R.classicalHalfPeriodSpace true) ≤ 2 := by
  let : FiniteDimensional ℂ (halfPeriodFullWeakRadical k true) :=
    diskRadical_finiteDimensional _ _
  have hle := LinearMap.finrank_le_finrank_of_injective
    (R.classicalHalfPeriodToFullRadical_injective true)
  have he : Module.finrank ℂ (halfPeriodFullWeakRadical k true) =
      diskWeakNullity (⊤ : Submodule ℂ ComplexH1) (surfacePotential k) := by
    change diskWeakNullity (mixedTraceDomain k true true) (surfacePotential k) = _
    rw [mixedTraceDomain_NN]
  exact hle.trans (he ▸ neumannRow_nullity_le_two hk)

/-- Distinct geometric rotation characters have trivial intersection. -/
lemma classicalHalfPeriodCharacter_inf_eq_bot (R : PaperHalfPeriodRealization k)
    (b : Bool) {i j : ℕ} (hij : FormIndex.zeta k ^ i ≠ FormIndex.zeta k ^ j) :
    R.classicalHalfPeriodCharacter b i ⊓ R.classicalHalfPeriodCharacter b j = ⊥ := by
  apply le_antisymm _ bot_le
  intro u hu
  rw [Submodule.mem_bot]
  apply Subtype.ext
  funext q
  have hi := hu.1 q
  have hj := hu.2 q
  have he : (FormIndex.zeta k ^ i - FormIndex.zeta k ^ j) * u.val q = 0 := by
    rw [sub_mul, ← hi, ← hj, sub_self]
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hij)

/-- Unrestricted bounded classical Neumann nullity on the actual half-period. -/
theorem classicalHalfPeriodNeumann_finrank_eq_two (R : PaperHalfPeriodRealization k)
    (hk : 3 ≤ k) : Module.finrank ℂ (R.classicalHalfPeriodSpace true) = 2 := by
  let : FiniteDimensional ℂ (R.classicalHalfPeriodSpace true) :=
    R.classicalHalfPeriodSpace_finiteDimensional true
  have hd (j : Fin k) : Module.finrank ℂ (R.classicalHalfPeriodCharacter true j) =
      if (j : ℕ) = 1 ∨ (j : ℕ) = k - 1 then 1 else 0 := by
    have he := (R.classicalHalfPeriodRadicalEquiv true j).finrank_eq
    exact he.trans (neumann_class_nullity k hk j)
  have h1 : Module.finrank ℂ (R.classicalHalfPeriodCharacter true 1) = 1 := by
    simpa using hd ⟨1, by omega⟩
  have h2 : Module.finrank ℂ (R.classicalHalfPeriodCharacter true (k-1)) = 1 := by
    simpa using hd ⟨k-1, by omega⟩
  have hz : FormIndex.zeta k ^ 1 ≠ FormIndex.zeta k ^ (k-1) := by
    intro he
    have hh := (FormIndex.zeta_prim (by omega : 0 < k)).pow_inj
      (by omega : 1 < k) (by omega : k-1 < k) he
    omega
  have hs := Submodule.finrank_sup_add_finrank_inf_eq
    (R.classicalHalfPeriodCharacter true 1) (R.classicalHalfPeriodCharacter true (k-1))
  rw [R.classicalHalfPeriodCharacter_inf_eq_bot true hz, finrank_bot, h1, h2] at hs
  have hl := Submodule.finrank_le
    (R.classicalHalfPeriodCharacter true 1 ⊔ R.classicalHalfPeriodCharacter true (k-1))
  have hu := R.classicalHalfPeriodNeumann_finrank_le_two hk
  omega

/-- Unrestricted bounded classical Dirichlet nullity on the actual half-period. -/
theorem classicalHalfPeriodDirichlet_finrank_eq_one (R : PaperHalfPeriodRealization k) :
    Module.finrank ℂ (R.classicalHalfPeriodSpace false) = 1 := by
  let : FiniteDimensional ℂ (R.classicalHalfPeriodSpace false) :=
    R.classicalHalfPeriodSpace_finiteDimensional false
  let S := Submodule.span ℂ {radialDirichletH1 h.out}
  have hmem (u : R.classicalHalfPeriodSpace false) :
      R.classicalHalfPeriodToH1 false u ∈ S := by
    obtain ⟨c, hc⟩ := generalDirichlet_kernel_span h.out
      (R.classicalHalfPeriodToH1 false u)
      ((R.classicalHalfPeriodData u).toDisk.dirichlet_mem_zeroTrace h.out)
      ((R.classicalHalfPeriodData u).toDisk.dirichlet_tests_zero h.out)
    exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
  let L : R.classicalHalfPeriodSpace false →ₗ[ℂ] S :=
    (R.classicalHalfPeriodToH1 false).codRestrict S hmem
  have hi : Function.Injective L := by
    intro u v he
    exact R.classicalHalfPeriodToH1_injective false (congrArg Subtype.val he)
  have hu := LinearMap.finrank_le_finrank_of_injective hi
  have hS : Module.finrank ℂ S ≤ 1 := by
    simpa [S] using (finrank_span_le_card ({radialDirichletH1 h.out} : Set ComplexH1))
  have hd : Module.finrank ℂ (R.classicalHalfPeriodCharacter false 0) = 1 := by
    have he := (R.classicalHalfPeriodRadicalEquiv false 0).finrank_eq
    have hn := pureSector_dirichlet_nullity_gen h.out (j := 0)
      (by have := h.out; omega)
    apply he.trans
    change diskWeakNullity (mixedCharacterDomain k 0 false false) (surfacePotential k) = 1
    simpa using hn
  have hl := Submodule.finrank_le (R.classicalHalfPeriodCharacter false 0)
  omega

end KsIndex.KarcherData.PaperHalfPeriodRealization
