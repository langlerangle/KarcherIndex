module

public import KsIndexLean.SectorInfinite
public import KsIndexLean.ZarembaUpper

@[expose] public section


/-!
# Variational bracketing and Zaremba nullity without an infinitude assumption

`sector_eigenbasisIndex_infinite` supplies the eigenbasis-index infinitude needed
by the imported bracketing and Zaremba estimates. The wrappers here discharge
that assumption locally. Their geometric, class-range and boundary-choice
hypotheses remain explicit.

The original statements with infinitude assumptions remain available.
`sector_eigenbasisIndex_infinite` is a theorem rather than a global instance;
these proofs supply it for the specific character domains they use.

-/

noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical KsIndex.Trace
open KsIndex.SingleDisk KsIndex.SingleDiskBridge KsIndex.Capstone

/-! ### Variational bracketing

The statements below use `negativeIndex` and the radical's `finrank`, valued
in `ℕ∞`, so their types do not require a spectral-count instance. The corresponding
`diskNegativeCount` statements use an infinite eigenbasis index in their types
and retain that explicit instance requirement. The identity
`disk_negativeIndex_eq_count` relates the variational and count formulations. -/

section BrickB
variable {k : ℕ}

/-- First bracketing inequality in variational form, with eigenbasis infinitude discharged. -/
theorem sector_weakIndex_add_nullity_le_mixed_uncond (hk : 0 < k) (j : ℕ) (b : Bool) :
    KsIndex.NegativeDensity.negativeIndex
        (fun u : mixedCharacterDomain k j false false =>
          (weakJacobi (surfacePotential k) u u).re) +
      (Module.finrank ℂ (@formRadical (mixedCharacterDomain k j false false)
        inferInstance (diskDomain_innerProductSpace _)
        (domainJacobiForm _ (surfacePotential k))) : ℕ∞)
      ≤ KsIndex.NegativeDensity.negativeIndex
        (fun u : mixedCharacterDomain k j b (!b) =>
          (weakJacobi (surfacePotential k) u u).re) := by
  have := sector_eigenbasisIndex_infinite k hk j false false
  have := sector_eigenbasisIndex_infinite k hk j b (!b)
  exact sector_weakIndex_add_nullity_le_mixed hk j b

/-- Second bracketing inequality in variational form, with eigenbasis infinitude discharged. -/
theorem sector_weakIndex_add_nullity_le_neumann_uncond (hk : 0 < k) (j : ℕ)
    (b1 b0 : Bool) (hb : b1 = false ∨ b0 = false) :
    KsIndex.NegativeDensity.negativeIndex
        (fun u : mixedCharacterDomain k j b1 b0 =>
          (weakJacobi (surfacePotential k) u u).re) +
      (Module.finrank ℂ (@formRadical (mixedCharacterDomain k j b1 b0)
        inferInstance (diskDomain_innerProductSpace _)
        (domainJacobiForm _ (surfacePotential k))) : ℕ∞)
      ≤ KsIndex.NegativeDensity.negativeIndex
        (fun u : mixedCharacterDomain k j true true =>
          (weakJacobi (surfacePotential k) u u).re) := by
  have := sector_eigenbasisIndex_infinite k hk j b1 b0
  have := sector_eigenbasisIndex_infinite k hk j true true
  exact sector_weakIndex_add_nullity_le_neumann hk j b1 b0 hb

end BrickB

/-! ### Zaremba nullity bounds -/

section BrickC
variable {k r : ℕ} {b1 b0 : Bool}

/-- Edge classes `r ∈ {0,1,k−1}` have vanishing
Zaremba nullity for distinct boundary flags and `k ≥ 3`. -/
theorem zaremba_nullity_zero_edge_uncond (hk : 3 ≤ k)
    (hr : r = 0 ∨ r = 1 ∨ r = k - 1) (hb : b1 ≠ b0) :
    diskWeakNullity (mixedCharacterDomain k r b1 b0) (surfacePotential k) = 0 := by
  have := sector_eigenbasisIndex_infinite k (by omega) r b1 b0
  have := sector_eigenbasisIndex_infinite k (by omega) r true true
  exact zaremba_nullity_zero_edge hk hr hb

/-- For `k ≥ 3`, distinct boundary flags and `2 ≤ r ≤ k−2`, Zaremba
nullity is at most one; eigenbasis infinitude is discharged locally. -/
theorem zaremba_nullity_le_one_middle_uncond (hk : 3 ≤ k)
    (h2 : 2 ≤ r) (hrk : r ≤ k - 2) (hb : b1 ≠ b0) :
    diskWeakNullity (mixedCharacterDomain k r b1 b0) (surfacePotential k) ≤ 1 := by
  have := sector_eigenbasisIndex_infinite k (by omega) r b1 b0
  have := sector_eigenbasisIndex_infinite k (by omega) r true true
  exact zaremba_nullity_le_one_middle hk h2 hrk hb

end BrickC
end KsIndex.Spectral
