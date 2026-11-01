module

public import KsIndexLean.KarcherHalfPeriodBoundary

@[expose] public section


/-!
# Integer-height arc images: `ewcover` item (3) for all `n : ℤ`

The paper's half-period boundary heights `0` and `π` identify with the alternating arc families
`Θ[k,0]` and `Θ[k,1]` (`halfPeriod_height_zero_iff_arc`, `halfPeriod_height_pi_iff_arc`). Here we
extend to every integer height `nπ` (`n : ℤ`, including negative `n`). Given a half-period
representative over a finite parameter `w`, a lift point at normalized height `nπ` exists iff
`w` lies on `Surface.arc k (n % 2).toNat`. The final set-image theorem removes the representative
hypothesis for the fixed reflection basepoint and a continuous EW extension.

The mechanism is the deck group `HeightLift.deck` (vertical period `2π`): a deck shift moves the
normalized height `HeightLift.height + π` by `2π = 2·π`, so `nπ` reduces mod `2π` to the `{0,π}`
base case of parity `n`, and `Surface.arc k j` depends on `j` only through `(-1)^j`.
`Int.emod` keeps the parity index in `{0,1}` for negative `n`, so the result is over all of `ℤ`.
-/
noncomputable section
namespace KsIndex.KarcherData
open Set

/-- **`ewcover` item (3) at every integer height.** For a finite parameter `w` with `[0,π]`
representative `q`, a lift point over `w` at normalized height `nπ` (`n : ℤ`) exists iff `w` lies on
the arc of parity `n`. The `n = 0, 1` cases are `halfPeriod_height_{zero,pi}_iff_arc`; all other
integers (and negatives) follow by deck shifts of period `2π`. -/
theorem halfPeriod_height_intMul_pi_iff_arc {k : ℕ} (hk : 2 ≤ k)
    (b w : PuncturedPlane k) (hb : b.val = 1) (C : PeriodTarget)
    (q : PaperHalfPeriod hk b C) (hq : HeightLift.projection q.val = finiteParameter w) (n : ℤ) :
    (∃ r : PeriodicEWCarrier hk b C,
        HeightLift.projection r = finiteParameter w ∧
        HeightLift.height r + Real.pi = (n : ℝ) * Real.pi)
      ↔ w.val ∈ Surface.arc k (n % 2).toNat := by
  have hpi := Real.pi_pos
  have hlo : 0 ≤ HeightLift.height q.val + Real.pi := q.property.1
  have hhi : HeightLift.height q.val + Real.pi ≤ Real.pi := q.property.2
  constructor
  · rintro ⟨r, hrp, hrh⟩
    -- same projection ⟹ `r` is a deck shift of `q`
    obtain ⟨j, hj⟩ := (HeightLift.same_projection_iff q.val r).mp (hq.trans hrp.symm)
    have hhr : HeightLift.height r = HeightLift.height q.val + (j : ℝ) * (2 * Real.pi) := by
      rw [← hj, HeightLift.height_deck]
    -- normalized height of `q` is `(n - 2j)·π`
    have key : HeightLift.height q.val + Real.pi = ((n - 2 * j : ℤ) : ℝ) * Real.pi := by
      rw [hhr] at hrh; push_cast at hrh ⊢; linear_combination hrh
    -- the `[0,π]` bound forces `n - 2j ∈ {0, 1}`
    have hdn' : (0 : ℤ) ≤ n - 2 * j := by
      have : (0 : ℝ) ≤ ((n - 2 * j : ℤ) : ℝ) := by nlinarith [key, hlo, hpi]
      exact_mod_cast this
    have hup' : n - 2 * j ≤ 1 := by
      have : ((n - 2 * j : ℤ) : ℝ) ≤ 1 := by nlinarith [key, hhi, hpi]
      exact_mod_cast this
    rcases (by omega : n - 2 * j = 0 ∨ n - 2 * j = 1) with h0 | h1
    · have hz : HeightLift.height q.val + Real.pi = 0 := by rw [key, h0]; push_cast; ring
      have hpar : (n % 2).toNat = 0 := by rw [show n % 2 = 0 from by omega, Int.toNat_zero]
      rw [hpar]
      exact (halfPeriod_height_zero_iff_arc hk b w hb C q hq).mp hz
    · have hz : HeightLift.height q.val + Real.pi = Real.pi := by rw [key, h1]; push_cast; ring
      have hpar : (n % 2).toNat = 1 := by rw [show n % 2 = 1 from by omega, Int.toNat_one]
      rw [hpar]
      exact (halfPeriod_height_pi_iff_arc hk b w hb C q hq).mp hz
  · intro harc
    rcases Int.emod_two_eq_zero_or_one n with h2 | h2
    · rw [h2, Int.toNat_zero] at harc
      have hz : HeightLift.height q.val + Real.pi = 0 :=
        (halfPeriod_height_zero_iff_arc hk b w hb C q hq).mpr harc
      have hnr : (n : ℝ) = 2 * ((n / 2 : ℤ) : ℝ) := by
        have : (2 : ℤ) * (n / 2) = n := by omega
        exact_mod_cast this.symm
      refine ⟨HeightLift.deck (n / 2) q.val, ?_, ?_⟩
      · rw [HeightLift.projection_deck]; exact hq
      · rw [HeightLift.height_deck]; linear_combination hz - Real.pi * hnr
    · rw [h2, Int.toNat_one] at harc
      have hz : HeightLift.height q.val + Real.pi = Real.pi :=
        (halfPeriod_height_pi_iff_arc hk b w hb C q hq).mpr harc
      have hnr : (n : ℝ) = 2 * ((n / 2 : ℤ) : ℝ) + 1 := by
        have : (2 : ℤ) * (n / 2) + 1 = n := by omega
        exact_mod_cast this.symm
      refine ⟨HeightLift.deck (n / 2) q.val, ?_, ?_⟩
      · rw [HeightLift.projection_deck]; exact hq
      · rw [HeightLift.height_deck]; linear_combination hz - Real.pi * hnr

/-- **`ewcover` item (3), set-image form (representative discharged).** Over basepoint
`reflectionBasepoint k` and a continuous EW extension `C`, the parameter projections of the lift
points at normalized height `nπ` are exactly the finite parameters on the arc of parity `n`. The
`[0,π]` representative hypothesis of `halfPeriod_height_intMul_pi_iff_arc` is discharged here:
forward, `sin(nπ) = 0` excludes points over infinity (`sin_lift_height_infinity`) and forces
`‖w‖ = 1` (`sin_lift_height_shift_zero_iff`), giving a disk representative; reverse, the arc's `‖w‖ = 1`
supplies one. -/
theorem halfPeriod_height_intMul_pi_image_arc {k : ℕ} [h : Fact (2 ≤ k)]
    (C : PeriodTarget)
    (hF : Continuous (extendedEWMap h.out (reflectionBasepoint k) C)) (n : ℤ) :
    HeightLift.projection '' {r : PeriodicEWCarrier h.out (reflectionBasepoint k) C |
        HeightLift.height r + Real.pi = (n : ℝ) * Real.pi}
      = finiteParameter '' {w : PuncturedPlane k | w.val ∈ Surface.arc k (n % 2).toNat} := by
  apply Set.Subset.antisymm
  · rintro p ⟨r, hrh, rfl⟩
    have hsin : Real.sin (HeightLift.height r + Real.pi) = 0 := by
      rw [hrh]; exact Real.sin_int_mul_pi n
    have hne : HeightLift.projection r ≠ infinityParameter k := by
      intro hi; rw [sin_lift_height_infinity C hF r hi] at hsin; norm_num at hsin
    rcases parameterSphere_cases (HeightLift.projection r) with hi | ⟨w, hw⟩
    · exact (hne hi).elim
    · have hnorm : ‖w.val‖ = 1 :=
        (sin_lift_height_shift_zero_iff h.out (reflectionBasepoint k) w rfl C r hw.symm).mp hsin
      obtain ⟨q, hq⟩ :=
        exists_halfPeriod_over_disk h.out (reflectionBasepoint k) w rfl C (le_of_eq hnorm)
      have harc : w.val ∈ Surface.arc k (n % 2).toNat :=
        (halfPeriod_height_intMul_pi_iff_arc h.out (reflectionBasepoint k) w rfl C q hq n).mp
          ⟨r, hw.symm, hrh⟩
      exact ⟨w, harc, hw⟩
  · rintro p ⟨w, harc, rfl⟩
    obtain ⟨q, hq⟩ :=
      exists_halfPeriod_over_disk h.out (reflectionBasepoint k) w rfl C (le_of_eq harc.1)
    obtain ⟨r, hrp, hrh⟩ :=
      (halfPeriod_height_intMul_pi_iff_arc h.out (reflectionBasepoint k) w rfl C q hq n).mpr harc
    exact ⟨r, hrh, hrp⟩

end KsIndex.KarcherData
