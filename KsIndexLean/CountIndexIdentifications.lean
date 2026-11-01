module

public import KsIndexLean.CountInequalityWiring
public import KsIndexLean.DiskNegativeIndex
public import KsIndexLean.JacobiRadicalCounts

@[expose] public section


/-!
# Spectral counts, variational index and radical dimension in character sectors

Converts the cross-count inequalities from `CountInequalityWiring` into statements
about index and nullity on `mixedCharacterDomain` sectors, corresponding to the
paper's Dirichlet–mixed–Neumann comparison:

    ind_D + nul_D ≤ ind_DN     and     ind_DN + nul_DN ≤ ind_N

with `ind` = `diskNegativeCount` (= the variational `negativeIndex`, by
`disk_negativeIndex_eq_count`) and `nul` = the finrank of the weak-form
radical (= `diskNonpositiveCount − diskNegativeCount`, by
`diskRadical_finrank_eq_count`).

The theorems retain explicit `[Infinite …]` hypotheses for the relevant spectral
eigenbasis index types. They do not construct these instances. The comparisons
assume `0 < k` and allow arbitrary character index `j`. The Neumann comparison
applies whenever at least one of the two boundary flags is `false`, including
the Dirichlet sector as well as the two mixed sectors.
-/

noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical KsIndex.Trace

variable (D : Submodule ℂ ComplexH1) [CompleteSpace D] (V : BoundedRealPotential)

/-- The nonpositive count decomposes as negative count + radical dimension
(with the counts ordered, so the ℕ subtraction is honest). -/
lemma diskNonpositiveCount_eq_negative_add_radical
    [Infinite (diskSpectralData D V).eigenbasisIndex] :
    diskNonpositiveCount D V = diskNegativeCount D V +
      Module.finrank ℂ (@formRadical D inferInstance
        (diskDomain_innerProductSpace D) (domainJacobiForm D V)) := by
  rw [diskRadical_finrank_eq_count]
  have h : diskNegativeCount D V ≤ diskNonpositiveCount D V :=
    strictSpectralCount_le_weakSpectralCount _ _ 0
  omega

section Sectors
variable {k : ℕ}

/-- **l.2450, first inequality, index objects (D → DN):**
`ind_D + nul_D ≤ ind_DN` at the character-sector level. -/
theorem sector_index_add_nullity_le_mixed (hk : 0 < k) (j : ℕ) (b : Bool)
    [Infinite (diskSpectralData (mixedCharacterDomain k j false false)
      (surfacePotential k)).eigenbasisIndex]
    [Infinite (diskSpectralData (mixedCharacterDomain k j b (!b))
      (surfacePotential k)).eigenbasisIndex] :
    diskNegativeCount (mixedCharacterDomain k j false false) (surfacePotential k) +
      Module.finrank ℂ (@formRadical (mixedCharacterDomain k j false false)
        inferInstance (diskDomain_innerProductSpace _)
        (domainJacobiForm _ (surfacePotential k)))
      ≤ diskNegativeCount (mixedCharacterDomain k j b (!b)) (surfacePotential k) := by
  rw [← diskNonpositiveCount_eq_negative_add_radical]
  exact mixed_dirichlet_infinite_cross_count hk j b

/-- **l.2450, second inequality, index objects (DN → N):**
`ind_DN + nul_DN ≤ ind_N` at the character-sector level. -/
theorem sector_index_add_nullity_le_neumann (hk : 0 < k) (j : ℕ)
    (b1 b0 : Bool) (hb : b1 = false ∨ b0 = false)
    [Infinite (diskSpectralData (mixedCharacterDomain k j b1 b0)
      (surfacePotential k)).eigenbasisIndex]
    [Infinite (diskSpectralData (mixedCharacterDomain k j true true)
      (surfacePotential k)).eigenbasisIndex] :
    diskNegativeCount (mixedCharacterDomain k j b1 b0) (surfacePotential k) +
      Module.finrank ℂ (@formRadical (mixedCharacterDomain k j b1 b0)
        inferInstance (diskDomain_innerProductSpace _)
        (domainJacobiForm _ (surfacePotential k)))
      ≤ diskNegativeCount (mixedCharacterDomain k j true true) (surfacePotential k) := by
  rw [← diskNonpositiveCount_eq_negative_add_radical]
  exact mixed_neumann_infinite_cross_count hk j b1 b0 hb

/-- The first comparison expressed using the variational `negativeIndex`,
with the radical dimension cast to `ℕ∞`. -/
theorem sector_weakIndex_add_nullity_le_mixed (hk : 0 < k) (j : ℕ) (b : Bool)
    [Infinite (diskSpectralData (mixedCharacterDomain k j false false)
      (surfacePotential k)).eigenbasisIndex]
    [Infinite (diskSpectralData (mixedCharacterDomain k j b (!b))
      (surfacePotential k)).eigenbasisIndex] :
    KsIndex.NegativeDensity.negativeIndex
        (fun u : mixedCharacterDomain k j false false =>
          (weakJacobi (surfacePotential k) u u).re) +
      (Module.finrank ℂ (@formRadical (mixedCharacterDomain k j false false)
        inferInstance (diskDomain_innerProductSpace _)
        (domainJacobiForm _ (surfacePotential k))) : ℕ∞)
      ≤ KsIndex.NegativeDensity.negativeIndex
        (fun u : mixedCharacterDomain k j b (!b) =>
          (weakJacobi (surfacePotential k) u u).re) := by
  rw [disk_negativeIndex_eq_count, disk_negativeIndex_eq_count]
  exact_mod_cast sector_index_add_nullity_le_mixed hk j b

/-- Second inequality, `ℕ∞`-cast. -/
theorem sector_weakIndex_add_nullity_le_neumann (hk : 0 < k) (j : ℕ)
    (b1 b0 : Bool) (hb : b1 = false ∨ b0 = false)
    [Infinite (diskSpectralData (mixedCharacterDomain k j b1 b0)
      (surfacePotential k)).eigenbasisIndex]
    [Infinite (diskSpectralData (mixedCharacterDomain k j true true)
      (surfacePotential k)).eigenbasisIndex] :
    KsIndex.NegativeDensity.negativeIndex
        (fun u : mixedCharacterDomain k j b1 b0 =>
          (weakJacobi (surfacePotential k) u u).re) +
      (Module.finrank ℂ (@formRadical (mixedCharacterDomain k j b1 b0)
        inferInstance (diskDomain_innerProductSpace _)
        (domainJacobiForm _ (surfacePotential k))) : ℕ∞)
      ≤ KsIndex.NegativeDensity.negativeIndex
        (fun u : mixedCharacterDomain k j true true =>
          (weakJacobi (surfacePotential k) u u).re) := by
  rw [disk_negativeIndex_eq_count, disk_negativeIndex_eq_count]
  exact_mod_cast sector_index_add_nullity_le_neumann hk j b1 b0 hb

end Sectors
end KsIndex.Spectral
