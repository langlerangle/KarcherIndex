module

public import KsIndexLean.CapstoneM2

@[expose] public section


/-!
# The m=2 index formula under reflection-encoding density

The sector decomposition and value assembly use `ReflEncodingDensity` alone.
They do not assume the separate `ArcEncodingDensity` hypothesis, whose
mixed-domain encoding caveat is explained in `SingleDiskNat`.
These theorems remain conditional on reflection-encoding density;
`KsIndex.Trace.reflEncodingDensity_holds` in `D5Discharge` supplies that hypothesis downstream.
-/

noncomputable section

namespace KsIndex.TwistSwap

open Complex KsIndex.Surface KsIndex.SurfaceForm KsIndex.SurfaceSym KsIndex.FormIndex
  KsIndex.Twisted KsIndex.Bracket KsIndex.SingleDiskBridge KsIndex.SingleDisk

variable {k : ℕ}

/-- `indSurface_two_eq`, from the reflection-encoding half alone. -/
theorem indSurface_two_eq_refl (hk : 2 ≤ k) (hR : ReflEncodingDensity k) :
    indSurface k 2
      = ∑ r : Fin k, (seamNat k true true (r : ℕ) + seamNat k false false (r : ℕ)
          + seamNat k false true (r : ℕ) + seamNat k true false (r : ℕ)) := by
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

/-- `indSurface_two_eq_DN`, from the reflection-encoding half alone. -/
theorem indSurface_two_eq_DN_refl (hk : 2 ≤ k) (hR : ReflEncodingDensity k) :
    indSurface k 2
      = ∑ r : Fin k, (seamNat k false false (r : ℕ) + 2 * seamNat k true false (r : ℕ)
          + seamNat k true true (r : ℕ)) := by
  rw [indSurface_two_eq_refl hk hR]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [seamNat_mixed hk (r : ℕ), two_mul]
  abel

end KsIndex.TwistSwap

namespace KsIndex.Capstone

open KsIndex.Surface KsIndex.SingleDisk KsIndex.SingleDiskBridge KsIndex.FormIndex
open KsIndex.TwistSwap

variable {k : ℕ}

/-- **THE m=2 INDEX CAPSTONE, reflection-encoding hypothesis only**:
`ind(Ξ_{k,2}) = 4k − 3` for every `k ≥ 3` under `ReflEncodingDensity k`
alone. The hypothesis is discharged separately in `D5Discharge`. -/
theorem indSurface_two_val_refl (hk : 3 ≤ k) (hR : ReflEncodingDensity k) :
    indSurface k 2 = ((4 * k - 3 : ℕ) : ℕ∞) := by
  have hcell : ∀ r : Fin k,
      seamNat k false false (r : ℕ) + 2 * seamNat k true false (r : ℕ)
        + seamNat k true true (r : ℕ)
      = ((2 + ttVal k (r : ℕ) : ℕ) : ℕ∞) := by
    intro r
    rw [seamNat_FF hk, seamNat_TF_eq_one hk r.isLt, seamNat_TT_eq hk r.isLt,
      mul_one, zero_add]
    push_cast
    rfl
  rw [indSurface_two_eq_DN_refl (by omega) hR,
    Finset.sum_congr rfl (fun r _ => hcell r), ← Nat.cast_sum]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun r => 2 + ttVal k r) k, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_range, smul_eq_mul, sum_ttVal hk]
  omega

/-- The index half of `Theorem_m2`, under the reflection-encoding hypothesis
for every `k`. -/
theorem theorem_m2_index_refl (hR : ∀ k, 3 ≤ k → ReflEncodingDensity k) :
    ∀ k, 3 ≤ k → indSurface k 2 = ((4 * k - 3 : ℕ) : ℕ∞) :=
  fun k hk => indSurface_two_val_refl hk (hR k hk)

end KsIndex.Capstone
