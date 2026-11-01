module

/-
KsIndexLean — TwistAssembly: the m = 2 index decomposition.

Each translation phase ζ = ±1 splits into two reflection cells with signs
(εζ, ε), where ε = ±1. The four cells give the Neumann, Dirichlet and two mixed
seam counts in each rotation character.

Under `EncodingDensity k` and `k ≥ 2`, `indSurface_two_eq` identifies the surface
index with the sum of these four seam counts. `indSurface_two_eq_DN` uses the
mixed-orientation equality to combine the two mixed columns. Numerical values
of the seam counts are separate inputs to subsequent index formulas.

`EncodingDensity` bundles the arc-encoding and reflection-encoding index
identities. The assembly theorems here keep this bundle as an explicit hypothesis.
-/
public import KsIndexLean.TwistTransport
public import KsIndexLean.SingleDiskNat

@[expose] public section


noncomputable section

open Complex MeasureTheory
open scoped ContDiff

namespace KsIndex.TwistSwap

open KsIndex.Surface KsIndex.SurfaceForm KsIndex.SurfaceSym KsIndex.FormIndex KsIndex.Twisted
  KsIndex.Bracket KsIndex.SingleDiskBridge KsIndex.SingleDisk

variable {k : ℕ}

/-! ### The encoding hypotheses -/

/-- Reflection-encoded and natural single-disk domains have equal index in
 each rotation character. The Boolean signs use `true ↦ 1` and `false ↦ -1`. -/
def ReflEncodingDensity (k : ℕ) : Prop :=
  ∀ (b₁ b₀ : Bool) (r : ℕ),
    formIndex (Qd k) (ReflCc k (SingleDisk.sgn b₁) (SingleDisk.sgn b₀) ⊓ Erot1 k r)
      = seamNat k b₁ b₀ r

/-- The arc-encoding and reflection-encoding index identities used by the
`m = 2` assembly. -/
def EncodingDensity (k : ℕ) : Prop :=
  ArcEncodingDensity k ∧ ReflEncodingDensity k

/-! ### The per-sector split into the two reflection cells -/

/-- **Per-sector reflection split.**  A single flux sector `ζ` (with `ζ² = 1`) of `Ξ_{k,2}` splits,
into the two reflection cells `ReflCc ζ 1` (the `ε = +1` swap-part) and
`ReflCc (−ζ) (−1)` (the `ε = −1` swap-part) on copy `0`. -/
lemma sector_reflcc_split (hk : 2 ≤ k) {ζ : ℂ} (hζ2 : ζ ^ 2 = 1) (hζ1 : ‖ζ‖ = 1) (hζ0 : ζ ≠ 0)
    (r : ℕ) :
    formIndex (Qs k 2)
        ((Dom k 2 ⊓ Module.End.eigenspace (rotE 2 (rotUnit k : ℂ)) (zeta k ^ r))
          ⊓ Module.End.eigenspace (shiftE 2) ζ)
      = formIndex (Qd k) (ReflCc k ζ 1 ⊓ Erot1 k r)
        + formIndex (Qd k) (ReflCc k (-ζ) (-1) ⊓ Erot1 k r) := by
  have ha : ‖(rotUnit k : ℂ)‖ = 1 := Circle.norm_coe _
  have h1sq : (1 : ℂ) ^ 2 = 1 := one_pow 2
  have hm1sq : (-1 : ℂ) ^ 2 = 1 := by norm_num
  have h1n : ‖(1 : ℂ)‖ = 1 := norm_one
  have hm1n : ‖(-1 : ℂ)‖ = 1 := by rw [norm_neg, norm_one]
  rw [formIndex_sector_eq hζ1 hζ2, formIndex_DomTw_eq_c hζ0 ha,
    formIndex_swapTw_split_c hk hζ2 hζ1 hζ0,
    seam_transport_tw hζ2 h1sq hζ1 h1n, seam_transport_tw hζ2 hm1sq hζ1 hm1n]
  simp only [one_mul, neg_one_mul, Erot1]

/-! ### The m=2 index formula -/

/-- **The index of `Ξ_{k,2}` as the four-cell seam sum.**  Over the rotation classes `r < k`, the
index is the sum of the four Klein-cell seam counts (`NN + DD + ND + DN`), under the encoding
hypothesis.  This is the exact index half of the paper's m=2 decomposition. -/
theorem indSurface_two_eq (hk : 2 ≤ k) (hE : EncodingDensity k) :
    indSurface k 2
      = ∑ r : Fin k, (seamNat k true true (r : ℕ) + seamNat k false false (r : ℕ)
          + seamNat k false true (r : ℕ) + seamNat k true false (r : ℕ)) := by
  have hR := hE.2
  have h1sq : (1 : ℂ) ^ 2 = 1 := one_pow 2
  have hm1sq : (-1 : ℂ) ^ 2 = 1 := by norm_num
  have h1n : ‖(1 : ℂ)‖ = 1 := norm_one
  have hm1n : ‖(-1 : ℂ)‖ = 1 := by rw [norm_neg, norm_one]
  have h1ne : (1 : ℂ) ≠ 0 := one_ne_zero
  have hm1ne : (-1 : ℂ) ≠ 0 := by norm_num
  rw [indSurface_eq_sum_sectors hk]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, zeta_two]
  rw [sector_reflcc_split hk h1sq h1n h1ne (r : ℕ),
    sector_reflcc_split hk hm1sq hm1n hm1ne (r : ℕ)]
  simp only [neg_neg]
  have e1 := hR true true (r : ℕ)
  have e2 := hR false false (r : ℕ)
  have e3 := hR false true (r : ℕ)
  have e4 := hR true false (r : ℕ)
  simp only [SingleDisk.sgn_true, SingleDisk.sgn_false] at e1 e2 e3 e4
  rw [e1, e2, e3, e4]
  abel

/-- **The paper's m=2 decomposition** `ind = ind_D + 2·ind_DN + ind_N`: collapsing the two mixed
columns via `seamNat_mixed` (the screw congruence `ND = DN`). -/
theorem indSurface_two_eq_DN (hk : 2 ≤ k) (hE : EncodingDensity k) :
    indSurface k 2
      = ∑ r : Fin k, (seamNat k false false (r : ℕ) + 2 * seamNat k true false (r : ℕ)
          + seamNat k true true (r : ℕ)) := by
  rw [indSurface_two_eq hk hE]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [seamNat_mixed hk (r : ℕ), two_mul]
  abel

end KsIndex.TwistSwap
