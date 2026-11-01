module

public import KsIndexLean.CountIndexIdentifications
public import KsIndexLean.WeakHemisphereIndex
public import KsIndexLean.SlitReflectionNullity
public import KsIndexLean.CapstoneM2

@[expose] public section


/-!
# Zaremba index values and nullity upper bounds

For `k ≥ 3` and either mixed boundary orientation, `mixed_weak_index_one` gives
index one in every character class `r < k`, using `seamNat_TF_eq_one` and the
screw transport `seamNat_mixed`. The Neumann index is one in the edge classes
`r ∈ {0, 1, k−1}` and two in the middle window `2 ≤ r ≤ k−2`.

The comparison `sector_weakIndex_add_nullity_le_neumann` then yields the paper's
Zaremba upper bound: nullity zero in the edge classes (`1 + nul ≤ 1`), and nullity
at most one in the middle window (`1 + nul ≤ 2`). The middle window is empty at
`k = 3`. This file does not prove vanishing of middle-window nullity; that requires
the separate circle/Dirichlet-to-Neumann reduction.

The proof uses the mixed index value directly rather than the Dirichlet-side
lower comparison. The two nullity theorems retain explicit `Infinite` hypotheses
for the mixed and Neumann spectral eigenbasis index types. The index-value
lemmas have no such explicit hypotheses.
-/

noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical KsIndex.Trace
open KsIndex.SingleDisk KsIndex.SingleDiskBridge KsIndex.Capstone

variable {k r : ℕ} {b1 b0 : Bool}

/-- `diskWeakIndex` is the variational `negativeIndex` used in the sector comparison. -/
lemma diskWeakIndex_def (D : Submodule ℂ ComplexH1) (V : BoundedRealPotential) :
    diskWeakIndex D V =
      KsIndex.NegativeDensity.negativeIndex
        (fun u : D => (weakJacobi V u u).re) := rfl

/-- `diskWeakNullity` is the radical dimension used in the sector comparison. -/
lemma diskWeakNullity_def (D : Submodule ℂ ComplexH1) (V : BoundedRealPotential) :
    diskWeakNullity D V = Module.finrank ℂ (@formRadical D inferInstance
      (diskDomain_innerProductSpace D) (domainJacobiForm D V)) := rfl

/-- **(Z0)** `ind_{DN,r} = 1` — both seam orientations, every class `r < k`. -/
theorem mixed_weak_index_one (hk : 3 ≤ k) (hr : r < k) (hb : b1 ≠ b0) :
    diskWeakIndex (mixedCharacterDomain k r b1 b0) (surfacePotential k) = 1 := by
  rw [mixedCharacter_weak_index_eq_seamNat (by omega)]
  cases b1 <;> cases b0
  · exact absurd rfl hb
  · rw [seamNat_mixed (by omega)]
    exact seamNat_TF_eq_one hk hr
  · exact seamNat_TF_eq_one hk hr
  · exact absurd rfl hb

/-- **(Z1)** The Neumann row at the edge classes: `ind_{N,r} = 1` for
`r ∈ {0, 1, k−1}` (`neumannCount` values `0/1/1`, the class-0 zero mode
supplying the `+1`). -/
theorem neumann_weak_index_edge (hk : 3 ≤ k) (hr : r = 0 ∨ r = 1 ∨ r = k - 1) :
    diskWeakIndex (mixedCharacterDomain k r true true) (surfacePotential k) = 1 := by
  have : Fact (1 < k) := ⟨by omega⟩
  rw [pureNeumann_weak_index hk (by omega : r < k)]
  rcases hr with h | h | h
  · subst h
    rw [Nat.cast_zero, neumannCount_zero hk, ite_eq_left rfl, zero_add]
  · subst h
    rw [Nat.cast_one, neumannCount_one hk, ite_eq_right one_ne_zero, add_zero]
  · subst h
    have hcast : (((k - 1 : ℕ)) : ZMod k) = -1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k), ZMod.natCast_self, Nat.cast_one, zero_sub]
    rw [hcast, neumannCount_neg_one hk, ite_eq_right (neg_ne_zero.mpr one_ne_zero), add_zero]

/-- **(Z2)** The Neumann row in the middle window: `ind_{N,r} = 2` for
`2 ≤ r ≤ k−2` (no zero mode; window empty at `k = 3`). -/
theorem neumann_weak_index_middle (hk : 3 ≤ k) (h2 : 2 ≤ r) (hrk : r ≤ k - 2) :
    diskWeakIndex (mixedCharacterDomain k r true true) (surfacePotential k) = 2 := by
  have : NeZero k := ⟨by omega⟩
  have hrlt : r < k := by omega
  have hval : ((r : ZMod k)).val = r := by
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hrlt
  have hne : ((r : ℕ) : ZMod k) ≠ 0 := by
    intro h0
    rw [h0, ZMod.val_zero] at hval
    omega
  rw [pureNeumann_weak_index hk hrlt,
    neumannCount_two hk _ (by rw [hval]; exact h2) (by rw [hval]; exact hrk),
    ite_eq_right hne, add_zero]

/-- **(Z3, headline)** Edge classes have VANISHING Zaremba nullity — including
the paper's `j = 0` pair (`nul_{DN,0} = 0` here, `ind_{DN,0} = 1` = (Z0)).
Squeeze: `1 + nul ≤ ind_N = 1` through the mixed-to-Neumann comparison. -/
theorem zaremba_nullity_zero_edge (hk : 3 ≤ k)
    (hr : r = 0 ∨ r = 1 ∨ r = k - 1) (hb : b1 ≠ b0)
    [Infinite (diskSpectralData (mixedCharacterDomain k r b1 b0)
      (surfacePotential k)).eigenbasisIndex]
    [Infinite (diskSpectralData (mixedCharacterDomain k r true true)
      (surfacePotential k)).eigenbasisIndex] :
    diskWeakNullity (mixedCharacterDomain k r b1 b0) (surfacePotential k) = 0 := by
  have hb' : b1 = false ∨ b0 = false := by
    cases b1 <;> cases b0 <;> simp_all
  have hbr := sector_weakIndex_add_nullity_le_neumann (k := k)
    (by omega : 0 < k) r b1 b0 hb'
  rw [← diskWeakIndex_def (mixedCharacterDomain k r b1 b0) (surfacePotential k),
    ← diskWeakIndex_def (mixedCharacterDomain k r true true) (surfacePotential k),
    ← diskWeakNullity_def (mixedCharacterDomain k r b1 b0) (surfacePotential k),
    mixed_weak_index_one hk (by omega : r < k) hb,
    neumann_weak_index_edge hk hr] at hbr
  have hle : 1 + diskWeakNullity (mixedCharacterDomain k r b1 b0)
      (surfacePotential k) ≤ 1 := by
    exact_mod_cast hbr
  omega

/-- **(Z4, headline)** Middle window: Zaremba nullity ≤ 1
(`1 + nul ≤ ind_N = 2`). The closure to `0` is the circle/DtN reduction
(Zclasses), downstream of this module. -/
theorem zaremba_nullity_le_one_middle (hk : 3 ≤ k)
    (h2 : 2 ≤ r) (hrk : r ≤ k - 2) (hb : b1 ≠ b0)
    [Infinite (diskSpectralData (mixedCharacterDomain k r b1 b0)
      (surfacePotential k)).eigenbasisIndex]
    [Infinite (diskSpectralData (mixedCharacterDomain k r true true)
      (surfacePotential k)).eigenbasisIndex] :
    diskWeakNullity (mixedCharacterDomain k r b1 b0) (surfacePotential k) ≤ 1 := by
  have hb' : b1 = false ∨ b0 = false := by
    cases b1 <;> cases b0 <;> simp_all
  have hbr := sector_weakIndex_add_nullity_le_neumann (k := k)
    (by omega : 0 < k) r b1 b0 hb'
  rw [← diskWeakIndex_def (mixedCharacterDomain k r b1 b0) (surfacePotential k),
    ← diskWeakIndex_def (mixedCharacterDomain k r true true) (surfacePotential k),
    ← diskWeakNullity_def (mixedCharacterDomain k r b1 b0) (surfacePotential k),
    mixed_weak_index_one hk (by omega : r < k) hb,
    neumann_weak_index_middle hk h2 hrk] at hbr
  have hle : 1 + diskWeakNullity (mixedCharacterDomain k r b1 b0)
      (surfacePotential k) ≤ 2 := by
    exact_mod_cast hbr
  omega

end KsIndex.Spectral
