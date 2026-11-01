module

/-
Local chart equalities for the end field.

`endFieldWith p u idx` reads, at each `ζ`, the `glue` of copy `idx ζ` at the chart
image `σ_c(ζ) = p + ζ^m`.  Per `glue`'s `‖w‖≤1` split this is the DIRECT copy where
`σ_c(ζ)` lands in the closed disk, and the REFLECTED copy (through the seam inversion
`σ(w)=1/w̄`) where it lands outside.  These two pointwise identities are the bridge
between the field and the two PDE branches (`endComp_jacobi` / `endComp_reflected`);
they hold for an arbitrary copy assignment `idx`; no compatibility of that assignment
is asserted here.
-/
public import KsIndexLean.B2Foundation
public import KsIndexLean.Bracket

@[expose] public section


noncomputable section
open KsIndex.Surface KsIndex.EndChart
namespace KsIndex.B2

/-- **Direct (interior) branch.**  Where the chart image lands in the closed disk,
the end field reads copy `idx ζ` directly. -/
lemma endFieldWith_inside {m : ℕ} (p : ℂ) (u : ZMod (2 * m) → ℂ → ℂ)
    (idx : ℂ → ZMod (2 * m)) {ζ : ℂ} (h : ‖endChart p m ζ‖ ≤ 1) :
    endFieldWith p u idx ζ = u (idx ζ) (endChart p m ζ) := by
  unfold endFieldWith Surface.glue
  rw [if_pos h]

/-- **Reflected (exterior) branch.**  Where the chart image lands outside the closed
disk, the end field reads copy `idx ζ + 1` through the seam inversion `σ(w)=1/w̄`. -/
lemma endFieldWith_outside {m : ℕ} (p : ℂ) (u : ZMod (2 * m) → ℂ → ℂ)
    (idx : ℂ → ZMod (2 * m)) {ζ : ℂ} (h : 1 < ‖endChart p m ζ‖) :
    endFieldWith p u idx ζ = u (idx ζ + 1) (Bracket.σ (endChart p m ζ)) := by
  unfold endFieldWith Surface.glue
  rw [if_neg (not_le.mpr h), ← Bracket.σ_apply]

/-! ### The reflected seam germ `(glue u j) ∘ σ`

Besides `glue u j`, the field may locally agree with `(glue u j) ∘ σ`, which (by `σ² = id`,
`σ` the reflection `1/w̄`) reads the OPPOSITE copies: copy `j+1` directly on the punctured open disk and
copy `j` through inversion on the exterior. These are the two local germ laws the endField's `idx`
assignment must match across each seam branch (matching index pairs `(j,j)` for `glue u j`,
`(j+1, j−1)` for `(glue u j)∘σ`). -/

/-- Reflected germ, interior: `(glue u j)(σ w) = u (j+1) w` for `0 < ‖w‖ < 1`. -/
lemma glueSigma_inside {m : ℕ} (u : ZMod (2 * m) → ℂ → ℂ) (j : ZMod (2 * m)) {w : ℂ}
    (hw0 : w ≠ 0) (hw : ‖w‖ < 1) : Surface.glue u j (Bracket.σ w) = u (j + 1) w := by
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hσ : 1 < ‖Bracket.σ w‖ := by rw [Bracket.norm_σ]; exact (one_lt_inv₀ hpos).mpr hw
  unfold Surface.glue
  rw [if_neg (not_le.mpr hσ), ← Bracket.σ_apply, Bracket.σ_σ]

/-- Reflected germ, exterior: `(glue u j)(σ w) = u j (σ w)` for `1 < ‖w‖`. -/
lemma glueSigma_outside {m : ℕ} (u : ZMod (2 * m) → ℂ → ℂ) (j : ZMod (2 * m)) {w : ℂ}
    (hw : 1 < ‖w‖) : Surface.glue u j (Bracket.σ w) = u j (Bracket.σ w) := by
  have hpos : 0 < ‖w‖ := by linarith
  have hσ : ‖Bracket.σ w‖ ≤ 1 := by rw [Bracket.norm_σ]; exact (inv_le_one₀ hpos).mpr (le_of_lt hw)
  unfold Surface.glue
  rw [if_pos hσ]

end KsIndex.B2
