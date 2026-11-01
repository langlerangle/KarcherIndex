module

public import KsIndexLean.KarcherImagePeriods
public import KsIndexLean.EuclideanAxisMotions

@[expose] public section


/-! Every ambient Euclidean symmetry of the EW image preserves its axis. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open Complex Set
variable {k : ℕ} [h : Fact (2 ≤ k)] (R : PaperHalfPeriodRealization k)

def ImageSymmetry (F : EuclideanMotion) : Prop :=
  ∀ p, F.affine p ∈ R.spaceImage ↔ p ∈ R.spaceImage

def spaceTurn (c : ℂ) (p : SpacePoint) : SpacePoint := (c * p.1, p.2)

lemma spaceImmersion_deck (n : ℤ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    R.spaceImmersion (HeightLift.deck n q) = R.spaceImmersion q + (0, (n : ℝ) * (2 * Real.pi)) := by
  apply Prod.ext
  · change R.horizontalComplex q = R.horizontalComplex q + 0
    simp
  change (HeightLift.height q + (n : ℝ) * (2 * Real.pi)) + Real.pi =
    HeightLift.height q + Real.pi + (n : ℝ) * (2 * Real.pi)
  ring

lemma period_deck (n : ℤ) : TranslationPeriod R.spaceImage (0, (n : ℝ) * (2 * Real.pi)) := by
  intro p
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨HeightLift.deck (-n) q, ?_⟩
    rw [R.spaceImmersion_deck, hq]
    ext <;> simp
  · rintro ⟨q, rfl⟩
    exact ⟨HeightLift.deck n q, R.spaceImmersion_deck n q⟩

lemma mem_spaceTurn_phaseSq_iff (p : SpacePoint) :
    spaceTurn (screwPhase (k := k) ^ 2) p ∈ R.spaceImage ↔ p ∈ R.spaceImage := by
  have hh := (R.period_deck (-1) (spaceScrew (k := k) (spaceScrew (k := k) p))).trans
    ((R.mem_spaceScrew_iff _).trans (R.mem_spaceScrew_iff p))
  have he : spaceTurn (screwPhase (k := k) ^ 2) p =
      spaceScrew (k := k) (spaceScrew (k := k) p) + (0, ((-1 : ℤ) : ℝ) * (2 * Real.pi)) := by
    apply Prod.ext
    · simp [spaceTurn, spaceScrew, pow_two, mul_assoc]
    · dsimp [spaceTurn, spaceScrew]
      push_cast
      ring
  rw [he]
  exact hh

omit h in
lemma spaceTurn_surjective {c : ℂ} (hc : c ≠ 0) : Function.Surjective (spaceTurn c) := by
  intro p
  exact ⟨(c⁻¹ * p.1, p.2), by simp [spaceTurn, hc]⟩

lemma mem_spaceTurn_inv_iff {c : ℂ} (hc : c ≠ 0)
    (hs : ∀ p, spaceTurn c p ∈ R.spaceImage ↔ p ∈ R.spaceImage) (p : SpacePoint) :
    spaceTurn c⁻¹ p ∈ R.spaceImage ↔ p ∈ R.spaceImage := by
  have hh := hs (spaceTurn c⁻¹ p)
  simpa [spaceTurn, hc] using hh.symm

/-- Conjugating the known vertical period forces preservation of its direction. -/
theorem symmetry_vertical_direction {F : EuclideanMotion} (hF : R.ImageSymmetry F) :
    (F.affine.linear (0, 1)).1 = 0 := by
  have hp := R.period_deck 1
  have ht : TranslationPeriod R.spaceImage (F.affine.linear (0, 2 * Real.pi)) := by
    apply TranslationPeriod.transport F.affine.surjective hF (by simpa using hp)
    intro p
    simpa [add_comm] using F.affine.map_vadd p ((0 : ℂ), 2 * Real.pi)
  have hh := R.period_vertical ht
  have he : ((0 : ℂ), 2 * Real.pi) = (2 * Real.pi) • ((0 : ℂ), (1 : ℝ)) := by simp
  rw [he, map_smul] at hh
  change (2 * Real.pi) • (F.affine.linear (0, 1)).1 = 0 at hh
  exact (smul_eq_zero.mp hh).resolve_left (by positivity)

lemma phaseSq_ne_one : screwPhase (k := k) ^ 2 ≠ 1 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by have := h.out; omega)
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast h.out
  have hθ : 0 < 2 * Real.pi / (k : ℝ) := by positivity
  have hθ' : 2 * Real.pi / (k : ℝ) < 2 * Real.pi := by
    apply (div_lt_iff₀ hkpos).mpr
    nlinarith [Real.pi_pos]
  intro he
  have hh := congrArg Complex.re he
  have hp : screwPhase (k := k) ^ 2 = Complex.exp ((((2 * Real.pi / k : ℝ)) : ℂ) * I) := by
    unfold screwPhase
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hp, Complex.exp_ofReal_mul_I_re] at hh
  have hz := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos]) hθ').mp hh
  linarith

/-- The horizontal displacement of an arbitrary Euclidean image symmetry is zero. -/
theorem symmetry_axis_offset_zero {F : EuclideanMotion} (hF : R.ImageSymmetry F) :
    (F.affine 0).1 = 0 := by
  obtain ⟨c, ε, hc, hε, hd | hd⟩ := F.axis_direction_normal_form (R.symmetry_vertical_direction hF)
  · let d := screwPhase (k := k) ^ 2
    have hdn : d ≠ 0 := pow_ne_zero _ screwPhase_ne_zero
    have hp : TranslationPeriod R.spaceImage ((1 - d) * (F.affine 0).1, 0) := by
      apply TranslationPeriod.of_intertwining F.affine.surjective (spaceTurn_surjective hdn)
        hF R.mem_spaceTurn_phaseSq_iff R.mem_spaceTurn_phaseSq_iff
      intro p
      rw [hd (spaceTurn _ p)]
      rw [hd p]
      apply Prod.ext <;> dsimp [spaceTurn, d] <;> ring
    have hz := R.horizontal_period_zero hp
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (Ne.symm phaseSq_ne_one))
  · let d := screwPhase (k := k) ^ 2
    have hdn : d ≠ 0 := pow_ne_zero _ screwPhase_ne_zero
    have hdunit : starRingEnd ℂ d = d⁻¹ := by
      have hn : ‖d‖ = 1 := by simp [d, norm_pow, screwPhase_norm]
      apply mul_right_cancel₀ hdn
      rw [inv_mul_cancel₀ hdn, Complex.conj_mul', hn]
      norm_num
    have hp : TranslationPeriod R.spaceImage ((1 - d⁻¹) * (F.affine 0).1, 0) := by
      apply TranslationPeriod.of_intertwining F.affine.surjective
        (spaceTurn_surjective (inv_ne_zero hdn))
        hF R.mem_spaceTurn_phaseSq_iff (R.mem_spaceTurn_inv_iff hdn R.mem_spaceTurn_phaseSq_iff)
      intro p
      rw [hd (spaceTurn _ p)]
      rw [hd p]
      apply Prod.ext <;> dsimp [spaceTurn]
      · rw [map_mul, hdunit]
        ring
      · ring
    have hz := R.horizontal_period_zero hp
    apply (mul_eq_zero.mp hz).resolve_left
    intro he
    have hi : d⁻¹ = 1 := by linear_combination -he
    have hh : d = 1 := inv_eq_one.mp hi
    exact phaseSq_ne_one hh

/-- Axis preservation follows solely from the image symmetries and
checkerboard period obstruction, including in the case k=2. -/
theorem symmetry_preserves_axis {F : EuclideanMotion} (hF : R.ImageSymmetry F) (p : SpacePoint) :
    (F.affine p).1 = 0 ↔ p.1 = 0 := by
  obtain ⟨c, ε, hc, _, hd | hd⟩ := F.axis_direction_normal_form (R.symmetry_vertical_direction hF)
  all_goals
    rw [hd, R.symmetry_axis_offset_zero hF]
    have hc0 : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hc]; norm_num)
    simp [hc0]

end KsIndex.KarcherData.PaperHalfPeriodRealization
