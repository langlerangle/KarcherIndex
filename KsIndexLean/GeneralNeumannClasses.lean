module

public import KsIndexLean.GeneralNeumannRow

@[expose] public section


/-!
# The sum of Neumann sector nullities

Each character-sector radical consists of full weak-kernel elements, by
`surfaceJacobi_cyclic_tests_suffice` at the full domain. Distinct rotation
characters give independent subspaces, so the full-kernel dimension bound
from `GeneralNeumannRow` yields `Σ_{r<k} nul(NN, r) ≤ 2`.
The identification with `diskWeakNullity` uses `finrank_map_subtype_eq`.
-/

noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.FormIndex

variable {k : ℕ}

/-- **V5a**: an NN class-radical element kills every full test — the cyclic
averaging at the trivial trace constraint. -/
lemma nnClass_radical_full_kernel (hk : 0 < k) (j : ℕ)
    (u : ComplexH1) (hu : u ∈ mixedCharacterDomain k j true true)
    (hQ : ∀ v : ↥(mixedCharacterDomain k j true true),
      weakJacobi (surfacePotential k) u v.val = 0) :
    ∀ w : ComplexH1, weakJacobi (surfacePotential k) u w = 0 := by
  intro w
  refine surfaceJacobi_cyclic_tests_suffice hk j ⊤
    (fun v _ => Submodule.mem_top) u hu.2 ?_ w Submodule.mem_top
  intro v hv
  exact hQ ⟨v, (mixedTraceDomain_NN k).symm ▸ Submodule.mem_top, hv.2⟩

/-- The class-`j` NN radical, as an honest `ComplexH1` submodule. -/
def nnClassRadical (k j : ℕ) : Submodule ℂ ComplexH1 :=
  (@formRadical _ inferInstance
    (diskDomain_innerProductSpace (mixedCharacterDomain k j true true))
    (domainJacobiForm (mixedCharacterDomain k j true true)
      (surfacePotential k))).map
    (mixedCharacterDomain k j true true).subtype

lemma nnClassRadical_finrank (k j : ℕ) :
    Module.finrank ℂ ↥(nnClassRadical k j) =
      diskWeakNullity (mixedCharacterDomain k j true true) (surfacePotential k) :=
  Submodule.finrank_map_subtype_eq _ _

/-- Class radicals live inside the full-kernel submodule (V5a). -/
lemma nnClassRadical_le_fullKernel (hk : 0 < k) (j : ℕ) :
    nnClassRadical k j ≤
      (@formRadical ↥(⊤ : Submodule ℂ ComplexH1) inferInstance
        (diskDomain_innerProductSpace (⊤ : Submodule ℂ ComplexH1))
        (domainJacobiForm (⊤ : Submodule ℂ ComplexH1)
          (surfacePotential k))).map
        (⊤ : Submodule ℂ ComplexH1).subtype := by
  rintro x ⟨u, hu, rfl⟩
  have hker : (⟨u.val, Submodule.mem_top⟩ : ↥(⊤ : Submodule ℂ ComplexH1)) ∈
      @formRadical ↥(⊤ : Submodule ℂ ComplexH1) inferInstance
        (diskDomain_innerProductSpace (⊤ : Submodule ℂ ComplexH1))
        (domainJacobiForm (⊤ : Submodule ℂ ComplexH1) (surfacePotential k)) := by
    rw [mem_formRadical]
    intro w
    rw [domainJacobiForm_apply]
    apply nnClass_radical_full_kernel hk j u.val u.property
    intro v
    have h := (mem_formRadical _ u).mp hu v
    rwa [domainJacobiForm_apply] at h
  exact Submodule.mem_map.mpr ⟨_, hker, rfl⟩

/-- Class radicals live inside the rotation eigenspaces. -/
lemma nnClassRadical_le_eigenspace (k j : ℕ) :
    nnClassRadical k j ≤
      Module.End.eigenspace
        (diskRotation (-(2 * Real.pi) / k)).toLinearMap (zeta k ^ j) := by
  rintro x ⟨u, _, rfl⟩
  rw [Module.End.mem_eigenspace_iff]
  exact (mem_weakCharacterDomain _ _ u.val).mp u.property.2

/-- **V5 headline**: the Neumann classes' nullities sum under the row bound. -/
theorem neumann_classes_nullity_sum_le_two (hk : 3 ≤ k) :
    (∑ r : Fin k, diskWeakNullity (mixedCharacterDomain k (r : ℕ) true true)
      (surfacePotential k)) ≤ 2 := by
  have hk0 : 0 < k := by omega
  -- the family is independent: distinct eigenvalues of one endomorphism
  have hzinj : Function.Injective (fun r : Fin k => zeta k ^ (r : ℕ)) := by
    intro r₁ r₂ h
    exact Fin.ext ((zeta_prim hk0).pow_inj r₁.isLt r₂.isLt h)
  have hindep : iSupIndep (fun r : Fin k => nnClassRadical k (r : ℕ)) :=
    ((Module.End.eigenspaces_iSupIndep _).comp hzinj).mono
      (fun r => nnClassRadical_le_eigenspace k r)
  -- the kernel target and its budget (V4)
  set K := (@formRadical ↥(⊤ : Submodule ℂ ComplexH1) inferInstance
    (diskDomain_innerProductSpace (⊤ : Submodule ℂ ComplexH1))
    (domainJacobiForm (⊤ : Submodule ℂ ComplexH1) (surfacePotential k))).map
    (⊤ : Submodule ℂ ComplexH1).subtype with hK
  have hcs : CompleteSpace ↥(⊤ : Submodule ℂ ComplexH1) :=
    (by rw [Submodule.top_coe]; exact isClosed_univ :
      IsClosed ((⊤ : Submodule ℂ ComplexH1) : Set ComplexH1)).completeSpace_coe
  have hfinR : FiniteDimensional ℂ
      ↥(@formRadical ↥(⊤ : Submodule ℂ ComplexH1) inferInstance
        (diskDomain_innerProductSpace (⊤ : Submodule ℂ ComplexH1))
        (domainJacobiForm (⊤ : Submodule ℂ ComplexH1) (surfacePotential k))) :=
    diskRadical_finiteDimensional (⊤ : Submodule ℂ ComplexH1) (surfacePotential k)
  have hfinK : FiniteDimensional ℂ ↥K := by
    rw [hK]
    exact Module.Finite.map _ _
  have hKle : Module.finrank ℂ ↥K ≤ 2 := by
    have he : Module.finrank ℂ ↥K =
        diskWeakNullity (⊤ : Submodule ℂ ComplexH1) (surfacePotential k) := by
      rw [hK]
      exact Submodule.finrank_map_subtype_eq _ _
    rw [he]
    exact neumannRow_nullity_le_two hk
  -- the direct-sum injection into K
  have hle : ∀ r : Fin k, nnClassRadical k (r : ℕ) ≤ K := fun r => by
    rw [hK]; exact nnClassRadical_le_fullKernel hk0 r
  classical
  let L : (DirectSum (Fin k) (fun r => ↥(nnClassRadical k (r : ℕ)))) →ₗ[ℂ] ComplexH1 :=
    DFinsupp.lsum ℕ (fun r => (nnClassRadical k (r : ℕ)).subtype)
  have hLinj : Function.Injective L := hindep.dfinsupp_lsum_injective
  have hrange : ∀ x : DirectSum (Fin k) (fun r => ↥(nnClassRadical k (r : ℕ))),
      L x ∈ K := by
    intro x
    rw [DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply]
    exact Submodule.sum_mem _ (fun r _ => hle r (x r).property)
  let L' : (DirectSum (Fin k) (fun r => ↥(nnClassRadical k (r : ℕ)))) →ₗ[ℂ] ↥K :=
    L.codRestrict K hrange
  have hL'inj : Function.Injective L' := by
    intro a b h
    exact hLinj (congrArg Subtype.val h)
  have hfinCl : ∀ r : Fin k, Module.Finite ℂ ↥(nnClassRadical k (r : ℕ)) :=
    fun r =>
      haveI := diskRadical_finiteDimensional
        (mixedCharacterDomain k (r : ℕ) true true) (surfacePotential k)
      Module.Finite.map _ _
  have hsum : (∑ r : Fin k, diskWeakNullity
      (mixedCharacterDomain k (r : ℕ) true true) (surfacePotential k)) =
      Module.finrank ℂ (DirectSum (Fin k) (fun r => ↥(nnClassRadical k (r : ℕ)))) := by
    rw [Module.finrank_directSum]
    exact Finset.sum_congr rfl fun r _ => (nnClassRadical_finrank k r).symm
  rw [hsum]
  calc Module.finrank ℂ (DirectSum (Fin k) (fun r => ↥(nnClassRadical k (r : ℕ))))
      ≤ Module.finrank ℂ ↥K := LinearMap.finrank_le_finrank_of_injective hL'inj
    _ ≤ 2 := hKle

end KsIndex.Spectral
