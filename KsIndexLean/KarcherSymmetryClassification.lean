module

public import KsIndexLean.KarcherImageRotations
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

@[expose] public section


/-! For a normalized EW realization with `k ≥ 2`, classify the affine Euclidean
motions preserving its image. The normal forms combine integral screw shifts,
rotations through multiples of `2π/k`, and coordinate-plane reflections. Both
directions are proved, without assuming a lift to the parameter surface. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open Complex Set
variable {k : ℕ} [h : Fact (2 ≤ k)] (R : PaperHalfPeriodRealization k)

def spaceHelix (n : ℤ) (p : SpacePoint) : SpacePoint :=
  (screwPhase (k := k) ^ n * p.1, p.2 + (n : ℝ) * Real.pi)

omit h in
lemma spaceHelix_add (n m : ℤ) (p : SpacePoint) :
    spaceHelix (k := k) (n + m) p = spaceHelix (k := k) n (spaceHelix (k := k) m p) := by
  apply Prod.ext
  · simp [spaceHelix, zpow_add₀ screwPhase_ne_zero, mul_assoc]
  · dsimp [spaceHelix]
    push_cast
    ring

lemma mem_spaceHelix_iff (n : ℤ) (p : SpacePoint) :
    spaceHelix (k := k) n p ∈ R.spaceImage ↔ p ∈ R.spaceImage := by
  have hpos (n : ℕ) : ∀ p, spaceHelix (k := k) (n : ℤ) p ∈ R.spaceImage ↔ p ∈ R.spaceImage := by
    induction n with
    | zero => intro p; simp [spaceHelix]
    | succ n ih =>
      intro p
      rw [show ((n + 1 : ℕ) : ℤ) = 1 + (n : ℤ) by omega, spaceHelix_add]
      have he (q : SpacePoint) : spaceHelix (k := k) 1 q = spaceScrew (k := k) q := by
        simp [spaceHelix, spaceScrew]
      rw [he]
      exact (R.mem_spaceScrew_iff _).trans (ih p)
  cases n with
  | ofNat n => exact hpos n p
  | negSucc n =>
    have hh := hpos (n + 1) (spaceHelix (k := k) (Int.negSucc n) p)
    rw [← spaceHelix_add] at hh
    rw [show ((n + 1 : ℕ) : ℤ) + Int.negSucc n = 0 by omega] at hh
    simpa [spaceHelix] using hh.symm

lemma root_is_phase_even {c : ℂ} (hc : ‖c‖ = 1) (hk : c ^ k = 1) :
    ∃ j : ℤ, c = screwPhase (k := k) ^ (2 * j : ℤ) := by
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by have := h.out; omega)
  have he : Complex.exp ((k : ℂ) * ((c.arg : ℂ) * I)) = 1 := by
    rw [Complex.exp_nat_mul, unit_exp_arg hc, hk]
  obtain ⟨j, hj⟩ := Complex.exp_eq_one_iff.mp he
  refine ⟨j, ?_⟩
  rw [← unit_exp_arg hc]
  unfold screwPhase
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  apply mul_left_cancel₀ hk0
  calc
    _ = (j : ℂ) * (2 * Real.pi * I) := hj
    _ = _ := by field_simp

lemma mem_spaceTurn_phase_even_iff (j : ℤ) (p : SpacePoint) :
    spaceTurn (screwPhase (k := k) ^ (2 * j : ℤ)) p ∈ R.spaceImage ↔ p ∈ R.spaceImage := by
  have hh := (R.period_deck (-j) (spaceHelix (k := k) (2 * j) p)).trans
    (R.mem_spaceHelix_iff (2 * j) p)
  have he : spaceTurn (screwPhase (k := k) ^ (2 * j : ℤ)) p =
      spaceHelix (k := k) (2 * j) p + (0, ((-j : ℤ) : ℝ) * (2 * Real.pi)) := by
    apply Prod.ext
    · simp [spaceTurn, spaceHelix]
    · dsimp [spaceTurn, spaceHelix]
      push_cast
      ring
  rw [he]
  exact hh

lemma mem_spaceTurn_root_iff {c : ℂ} (hc : ‖c‖ = 1) (hk : c ^ k = 1) (p : SpacePoint) :
    spaceTurn c p ∈ R.spaceImage ↔ p ∈ R.spaceImage := by
  obtain ⟨j, rfl⟩ := root_is_phase_even hc hk
  exact R.mem_spaceTurn_phase_even_iff j p

lemma symmetry_vertical_offset {F : EuclideanMotion} (hF : R.ImageSymmetry F) :
    ∃ m : ℤ, (F.affine 0).2 = (m : ℝ) * Real.pi := by
  obtain ⟨c, ε, hc, hε, hd | hd⟩ := F.axis_direction_normal_form (R.symmetry_vertical_direction hF)
  all_goals
    have hp := (hF ((0 : ℂ), Real.pi / 2)).mpr R.axis_center_mem
    obtain ⟨q, hq⟩ := hp
    have hx : R.horizontalComplex q = 0 := by
      have hh := congrArg Prod.fst hq
      rw [hd (0, Real.pi / 2), R.symmetry_axis_offset_zero hF] at hh
      simpa [spaceImmersion] using hh
    have ha : R.OnVerticalAxis q := by
      constructor
      · simpa [horizontalComplex] using congrArg Complex.re hx
      · simpa [horizontalComplex] using congrArg Complex.im hx
    obtain ⟨n, hn⟩ := R.axis_height_half_integer q ha
    have hh := congrArg Prod.snd hq
    change HeightLift.height q + Real.pi = (F.affine (0, Real.pi / 2)).2 at hh
    rw [hd] at hh
    dsimp at hh
    rcases hε with hε | hε
    · refine ⟨n, ?_⟩
      rw [hε] at hh
      linarith
    · refine ⟨n + 1, ?_⟩
      rw [hε] at hh
      push_cast
      linarith

/-- The horizontal multiplier, after removing the integral screw shift, is a root of unity. -/
lemma symmetry_normalized_multiplier {F : EuclideanMotion} (hF : R.ImageSymmetry F)
    {c : ℂ} {ε : ℝ} {m : ℤ} (hc : ‖c‖ = 1) (hε : ε = 1 ∨ ε = -1)
    (hd : (∀ p, F.affine p = (c * p.1, ε * p.2 + (m : ℝ) * Real.pi)) ∨
      (∀ p, F.affine p = (c * starRingEnd ℂ p.1, ε * p.2 + (m : ℝ) * Real.pi))) :
    (screwPhase (k := k) ^ (-m) * c) ^ k = 1 := by
  apply R.image_rotation_root (by simp [norm_zpow, screwPhase_norm, hc])
  intro p
  rcases hd with hd | hd <;> rcases hε with rfl | rfl
  · have hh := (R.mem_spaceHelix_iff (-m) (F.affine p)).trans (hF p)
    simpa [spaceHelix, spaceTurn, hd, mul_assoc] using hh
  · have hh := (R.mem_spaceHelix_iff (-m) (F.affine (spaceReflectZ p))).trans
      ((hF _).trans (R.mem_spaceReflectZ_iff p))
    simpa [spaceHelix, spaceTurn, spaceReflectZ, hd, mul_assoc] using hh
  · have hh := (R.mem_spaceHelix_iff (-m) (F.affine (spaceReflectY p))).trans
      ((hF _).trans (R.mem_spaceReflectY_iff p))
    simpa [spaceHelix, spaceTurn, spaceReflectY, hd, mul_assoc] using hh
  · have hh := (R.mem_spaceHelix_iff (-m) (F.affine (spaceReflectY (spaceReflectZ p)))).trans
      ((hF _).trans ((R.mem_spaceReflectY_iff _).trans (R.mem_spaceReflectZ_iff p)))
    simpa [spaceHelix, spaceTurn, spaceReflectY, spaceReflectZ, hd, mul_assoc] using hh

/-- Every ambient symmetry is a screw shift, a rotation through an integral
multiple of 2π/k, and optional reflections in the two coordinate planes. -/
theorem image_symmetry_normal_form {F : EuclideanMotion} (hF : R.ImageSymmetry F) :
    ∃ (m j : ℤ) (ε : ℝ), (ε = 1 ∨ ε = -1) ∧
      ((∀ p, F.affine p = (screwPhase (k := k) ^ (m + 2 * j) * p.1,
          ε * p.2 + (m : ℝ) * Real.pi)) ∨
       (∀ p, F.affine p = (screwPhase (k := k) ^ (m + 2 * j) * starRingEnd ℂ p.1,
          ε * p.2 + (m : ℝ) * Real.pi))) := by
  obtain ⟨c, ε, hc, hε, hd⟩ := F.axis_direction_normal_form (R.symmetry_vertical_direction hF)
  obtain ⟨m, hm⟩ := R.symmetry_vertical_offset hF
  have hd' : (∀ p, F.affine p = (c * p.1, ε * p.2 + (m : ℝ) * Real.pi)) ∨
      (∀ p, F.affine p = (c * starRingEnd ℂ p.1, ε * p.2 + (m : ℝ) * Real.pi)) := by
    simpa [R.symmetry_axis_offset_zero hF, hm] using hd
  have hk := R.symmetry_normalized_multiplier hF hc hε hd'
  obtain ⟨j, hj⟩ := root_is_phase_even
    (by simp [norm_zpow, screwPhase_norm, hc]) hk
  have he : c = screwPhase (k := k) ^ (m + 2 * j) := by
    rw [zpow_add₀ screwPhase_ne_zero, ← hj, ← mul_assoc, ← zpow_add₀ screwPhase_ne_zero]
    simp
  exact ⟨m, j, ε, hε, by simpa [he] using hd'⟩

/-- Each of the explicit normal forms is indeed an image symmetry. -/
theorem image_symmetry_of_normal_form {F : EuclideanMotion}
    {m j : ℤ} {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hd : (∀ p, F.affine p = (screwPhase (k := k) ^ (m + 2 * j) * p.1,
        ε * p.2 + (m : ℝ) * Real.pi)) ∨
      (∀ p, F.affine p = (screwPhase (k := k) ^ (m + 2 * j) * starRingEnd ℂ p.1,
        ε * p.2 + (m : ℝ) * Real.pi))) : R.ImageSymmetry F := by
  intro p
  have hs (q : SpacePoint) := (R.mem_spaceHelix_iff m
    (spaceTurn (screwPhase (k := k) ^ (2 * j : ℤ)) q)).trans
      (R.mem_spaceTurn_phase_even_iff j q)
  rcases hd with hd | hd <;> rcases hε with rfl | rfl
  · rw [hd]
    simpa [spaceHelix, spaceTurn, zpow_add₀ screwPhase_ne_zero, mul_assoc] using hs p
  · rw [hd]
    simpa [spaceHelix, spaceTurn, spaceReflectZ, zpow_add₀ screwPhase_ne_zero, mul_assoc]
      using (hs (spaceReflectZ p)).trans (R.mem_spaceReflectZ_iff p)
  · rw [hd]
    simpa [spaceHelix, spaceTurn, spaceReflectY, zpow_add₀ screwPhase_ne_zero, mul_assoc]
      using (hs (spaceReflectY p)).trans (R.mem_spaceReflectY_iff p)
  · rw [hd]
    simpa [spaceHelix, spaceTurn, spaceReflectY, spaceReflectZ,
      zpow_add₀ screwPhase_ne_zero, mul_assoc] using
      (hs (spaceReflectY (spaceReflectZ p))).trans
        ((R.mem_spaceReflectY_iff _).trans (R.mem_spaceReflectZ_iff p))

/-- Full ambient symmetry classification, valid also for k=2. No lift of the
ambient symmetry to the parameter surface is assumed. -/
theorem image_symmetry_iff_normal_form (F : EuclideanMotion) :
    R.ImageSymmetry F ↔ ∃ (m j : ℤ) (ε : ℝ), (ε = 1 ∨ ε = -1) ∧
      ((∀ p, F.affine p = (screwPhase (k := k) ^ (m + 2 * j) * p.1,
          ε * p.2 + (m : ℝ) * Real.pi)) ∨
       (∀ p, F.affine p = (screwPhase (k := k) ^ (m + 2 * j) * starRingEnd ℂ p.1,
          ε * p.2 + (m : ℝ) * Real.pi))) := by
  constructor
  · exact R.image_symmetry_normal_form
  · rintro ⟨m, j, ε, hε, hd⟩
    exact R.image_symmetry_of_normal_form hε hd

omit h in
/-- A full vertical period is a word in the screw and vertical-plane reflection. -/
lemma period_word (p : SpacePoint) :
    spaceScrew (k := k) (spaceReflectY (spaceScrew (k := k) (spaceReflectY p))) =
      p + (0, 2 * Real.pi) := by
  apply Prod.ext
  · simp only [spaceScrew, spaceReflectY, map_mul, starRingEnd_self_apply,
      Prod.fst_add, ← mul_assoc, Complex.mul_conj', screwPhase_norm]
    norm_num
  · dsimp [spaceScrew, spaceReflectY]
    ring

end KsIndex.KarcherData.PaperHalfPeriodRealization
