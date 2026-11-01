module

public import KsIndexLean.CountInequalityTransfer
public import KsIndexLean.MixedDirichletStrictBracketing
public import KsIndexLean.MixedNeumannStrictBracketing

@[expose] public section


/-!
# Strict spectral-count comparisons for mixed disk domains

Apply the strict Dirichlet/mixed and mixed/Neumann eigenvalue inequalities to
`CountInequalityTransfer`. The four theorems cover infinite/infinite and
finite/infinite spectra, bounding the nonpositive count of the more constrained
problem by the negative count of the less constrained problem.

Each spectrum is shifted by the same `(surfacePotential k).C + 1`.
The infinite sequences are `infiniteReciprocalShift`, whose monotonicity is
proved by `infiniteReciprocalShift_monotone`. Thus their first-crossing indices
have the sublevel-count interpretation given in `OrderedSpectralCounts`.
The finite/infinite proofs pass that monotonicity theorem explicitly.
The Neumann comparisons require at least one Dirichlet boundary flag, excluding
the case of comparing the Neumann domain to itself.
-/

noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical KsIndex.Trace KsIndex.FormIndex

/-- **Count-level strict cross inequality (∞/∞, full-Dirichlet → mixed).** The paper's
`ind_D + nul_D ≤ ind_DN` (l.2450) at the count level: `nonpositiveCount(DD) ≤
negativeCount(DN)`, from the strict eigenvalue gap `mixed_dirichlet_infinite_eigenvalue_lt`
fed through `weakSpectralCount_le_strictSpectralCount_of_lt`. -/
lemma mixed_dirichlet_infinite_cross_count {k : ℕ} (hk : 0 < k) (j : ℕ) (b : Bool)
    [Infinite (diskSpectralData (mixedCharacterDomain k j false false)
      (surfacePotential k)).eigenbasisIndex]
    [Infinite (diskSpectralData (mixedCharacterDomain k j b (!b))
      (surfacePotential k)).eigenbasisIndex] :
    weakSpectralCount
        ((diskSpectralData (mixedCharacterDomain k j false false)
          (surfacePotential k)).infiniteReciprocalShift ((surfacePotential k).C + 1))
        ((diskSpectralData (mixedCharacterDomain k j false false)
          (surfacePotential k)).infiniteReciprocalShift_tendsto_atTop
          ((surfacePotential k).C + 1)) 0
      ≤ strictSpectralCount
        ((diskSpectralData (mixedCharacterDomain k j b (!b))
          (surfacePotential k)).infiniteReciprocalShift ((surfacePotential k).C + 1))
        ((diskSpectralData (mixedCharacterDomain k j b (!b))
          (surfacePotential k)).infiniteReciprocalShift_tendsto_atTop
          ((surfacePotential k).C + 1)) 0 :=
  weakSpectralCount_le_strictSpectralCount_of_lt _ _
    (fun n => mixed_dirichlet_infinite_eigenvalue_lt hk j b n) 0

/-- **Count-level strict cross inequality (∞/∞, mixed → Neumann).** The paper's
`ind_DN + nul_DN ≤ ind_N` (l.2450) at the count level: `nonpositiveCount(mixed) ≤
negativeCount(NN)`, from `mixed_neumann_infinite_eigenvalue_lt` (the `b1=false ∨ b0=false`
guard rules out the degenerate NN=NN case). -/
lemma mixed_neumann_infinite_cross_count {k : ℕ} (hk : 0 < k) (j : ℕ) (b1 b0 : Bool)
    (hb : b1 = false ∨ b0 = false)
    [Infinite (diskSpectralData (mixedCharacterDomain k j b1 b0)
      (surfacePotential k)).eigenbasisIndex]
    [Infinite (diskSpectralData (mixedCharacterDomain k j true true)
      (surfacePotential k)).eigenbasisIndex] :
    weakSpectralCount
        ((diskSpectralData (mixedCharacterDomain k j b1 b0)
          (surfacePotential k)).infiniteReciprocalShift ((surfacePotential k).C + 1))
        ((diskSpectralData (mixedCharacterDomain k j b1 b0)
          (surfacePotential k)).infiniteReciprocalShift_tendsto_atTop
          ((surfacePotential k).C + 1)) 0
      ≤ strictSpectralCount
        ((diskSpectralData (mixedCharacterDomain k j true true)
          (surfacePotential k)).infiniteReciprocalShift ((surfacePotential k).C + 1))
        ((diskSpectralData (mixedCharacterDomain k j true true)
          (surfacePotential k)).infiniteReciprocalShift_tendsto_atTop
          ((surfacePotential k).C + 1)) 0 :=
  weakSpectralCount_le_strictSpectralCount_of_lt _ _
    (fun n => mixed_neumann_infinite_eigenvalue_lt hk j b1 b0 hb n) 0

/-- **Count-level strict cross inequality (fin/∞, full-Dirichlet → mixed).** Tighter
(full-Dirichlet) sector finite-dimensional, mixed sector infinite. -/
lemma mixed_dirichlet_finite_to_infinite_cross_count {k : ℕ} (hk : 0 < k) (j : ℕ) (b : Bool)
    [FiniteDimensional ℂ (WeightedDiskAmbient (mixedCharacterDomain k j false false))]
    [Infinite (diskSpectralData (mixedCharacterDomain k j b (!b))
      (surfacePotential k)).eigenbasisIndex] :
    (Finset.univ.filter fun i =>
        (diskSpectralData (mixedCharacterDomain k j false false)
          (surfacePotential k)).finiteReciprocalShift ((surfacePotential k).C + 1) i ≤ 0).card
      ≤ strictSpectralCount
        ((diskSpectralData (mixedCharacterDomain k j b (!b))
          (surfacePotential k)).infiniteReciprocalShift ((surfacePotential k).C + 1))
        ((diskSpectralData (mixedCharacterDomain k j b (!b))
          (surfacePotential k)).infiniteReciprocalShift_tendsto_atTop
          ((surfacePotential k).C + 1)) 0 :=
  finite_weakCount_le_infStrictCount_of_lt _ _ _
    ((diskSpectralData (mixedCharacterDomain k j b (!b))
      (surfacePotential k)).infiniteReciprocalShift_monotone ((surfacePotential k).C + 1))
    (fun i => mixed_dirichlet_finite_to_infinite_eigenvalue_lt hk j b i.val i.isLt) 0

/-- **Count-level strict cross inequality (fin/∞, mixed → Neumann).** Mixed sector
finite-dimensional, Neumann sector infinite. -/
lemma mixed_neumann_finite_to_infinite_cross_count {k : ℕ} (hk : 0 < k) (j : ℕ)
    (b1 b0 : Bool) (hb : b1 = false ∨ b0 = false)
    [FiniteDimensional ℂ (WeightedDiskAmbient (mixedCharacterDomain k j b1 b0))]
    [Infinite (diskSpectralData (mixedCharacterDomain k j true true)
      (surfacePotential k)).eigenbasisIndex] :
    (Finset.univ.filter fun i =>
        (diskSpectralData (mixedCharacterDomain k j b1 b0)
          (surfacePotential k)).finiteReciprocalShift ((surfacePotential k).C + 1) i ≤ 0).card
      ≤ strictSpectralCount
        ((diskSpectralData (mixedCharacterDomain k j true true)
          (surfacePotential k)).infiniteReciprocalShift ((surfacePotential k).C + 1))
        ((diskSpectralData (mixedCharacterDomain k j true true)
          (surfacePotential k)).infiniteReciprocalShift_tendsto_atTop
          ((surfacePotential k).C + 1)) 0 :=
  finite_weakCount_le_infStrictCount_of_lt _ _ _
    ((diskSpectralData (mixedCharacterDomain k j true true)
      (surfacePotential k)).infiniteReciprocalShift_monotone ((surfacePotential k).C + 1))
    (fun i => mixed_neumann_finite_to_infinite_eigenvalue_lt hk j b1 b0 hb i.val i.isLt) 0

end KsIndex.Spectral
