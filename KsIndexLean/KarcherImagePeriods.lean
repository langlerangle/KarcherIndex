module

public import KsIndexLean.CheckerboardPeriods
public import KsIndexLean.KarcherCheckerboard
public import KsIndexLean.KarcherRealConjugation

@[expose] public section


/-! Translation periods of the actual EW image are necessarily vertical. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open Complex Set
variable {k : ℕ} [h : Fact (2 ≤ k)] (R : PaperHalfPeriodRealization k)

/-- Cartesian real three-space written as one complex horizontal coordinate
and one real vertical coordinate. -/
def spaceImmersion (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) : SpacePoint :=
  (R.horizontalComplex q, HeightLift.height q + Real.pi)

def spaceImage : Set SpacePoint := Set.range R.spaceImmersion

def screwPhase : ℂ := Complex.exp (((Real.pi / k : ℝ) : ℂ) * I)

def spaceScrew (p : SpacePoint) : SpacePoint := (screwPhase (k := k) * p.1, p.2 + Real.pi)
def spaceReflectY (p : SpacePoint) : SpacePoint := (starRingEnd ℂ p.1, p.2)
def spaceReflectZ (p : SpacePoint) : SpacePoint := (p.1, -p.2)

omit h in
lemma screwPhase_ne_zero : screwPhase (k := k) ≠ 0 := Complex.exp_ne_zero _
omit h in
lemma screwPhase_norm : ‖screwPhase (k := k)‖ = 1 := Complex.norm_exp_ofReal_mul_I _

lemma spaceImmersion_screw (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    R.spaceImmersion (R.screwLift q) = spaceScrew (k := k) (R.spaceImmersion q) := by
  apply Prod.ext
  · dsimp only [spaceImmersion, spaceScrew, horizontalComplex]
    rw [R.screwLift_ambient]
    dsimp only [PeriodTarget.rotate, projectPeriod, Prod.fst, Prod.snd]
    rw [Complex.re_add_im]
    have he : (Complex.exp (((-Real.pi / k : ℝ) : ℂ) * I))⁻¹ = screwPhase (k := k) := by
      rw [← Complex.exp_neg]
      unfold screwPhase
      congr 1
      push_cast
      ring
    rw [he]
  · exact R.screwLift_height q

lemma spaceImmersion_reflectY (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    R.spaceImmersion (R.conjugationLift q) = spaceReflectY (R.spaceImmersion q) := by
  apply Prod.ext
  · dsimp only [spaceImmersion, horizontalComplex, spaceReflectY]
    rw [R.conjugationLift_ambient]
    apply Complex.ext <;> simp
  · rfl

lemma spaceImmersion_reflectZ (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    R.spaceImmersion (lowerSeamLift R.C R.hC q) = spaceReflectZ (R.spaceImmersion q) := by
  apply Prod.ext
  · dsimp only [spaceImmersion, horizontalComplex, spaceReflectZ]
    rw [centeredLiftAmbient_lowerSeam]
  · exact lowerSeamLift_height R.C R.hC q

lemma mem_spaceReflectY_iff (p : SpacePoint) :
    spaceReflectY p ∈ R.spaceImage ↔ p ∈ R.spaceImage := by
  have hf : ∀ p ∈ R.spaceImage, spaceReflectY p ∈ R.spaceImage := by
    rintro _ ⟨q, rfl⟩
    exact ⟨R.conjugationLift q, R.spaceImmersion_reflectY q⟩
  constructor
  · intro hp
    simpa [spaceReflectY] using hf _ hp
  · exact hf p

lemma mem_spaceReflectZ_iff (p : SpacePoint) :
    spaceReflectZ p ∈ R.spaceImage ↔ p ∈ R.spaceImage := by
  have hf : ∀ p ∈ R.spaceImage, spaceReflectZ p ∈ R.spaceImage := by
    rintro _ ⟨q, rfl⟩
    exact ⟨lowerSeamLift R.C R.hC q, R.spaceImmersion_reflectZ q⟩
  constructor
  · intro hp
    simpa [spaceReflectZ] using hf _ hp
  · exact hf p

omit h in
lemma spaceScrew_surjective : Function.Surjective (spaceScrew (k := k)) := by
  intro p
  refine ⟨((screwPhase (k := k))⁻¹ * p.1, p.2 - Real.pi), ?_⟩
  simp [spaceScrew, screwPhase_ne_zero]

lemma mem_spaceScrew_iff (p : SpacePoint) :
    spaceScrew (k := k) p ∈ R.spaceImage ↔ p ∈ R.spaceImage := by
  have hf : ∀ p ∈ R.spaceImage, spaceScrew (k := k) p ∈ R.spaceImage := by
    rintro _ ⟨q, rfl⟩
    exact ⟨R.screwLift q, R.spaceImmersion_screw q⟩
  constructor
  · intro hp
    have h1 := (R.mem_spaceReflectZ_iff _).mpr ((R.mem_spaceReflectY_iff _).mpr hp)
    have h2 := hf _ h1
    have h3 := (R.mem_spaceReflectY_iff _).mpr ((R.mem_spaceReflectZ_iff _).mpr h2)
    have hc : starRingEnd ℂ (screwPhase (k := k)) * screwPhase (k := k) = 1 := by
      rw [Complex.conj_mul', screwPhase_norm]
      norm_num
    simpa [spaceScrew, spaceReflectY, spaceReflectZ, map_mul, ← mul_assoc, hc] using h3
  · exact hf p

lemma period_screw {v : SpacePoint} (hv : TranslationPeriod R.spaceImage v) :
    TranslationPeriod R.spaceImage (screwPhase (k := k) * v.1, v.2) := by
  apply TranslationPeriod.transport spaceScrew_surjective R.mem_spaceScrew_iff hv
  intro p
  apply Prod.ext
  · simp [spaceScrew, mul_add]
  · dsimp [spaceScrew]
    ring

lemma period_reflectZ {v : SpacePoint} (hv : TranslationPeriod R.spaceImage v) :
    TranslationPeriod R.spaceImage (spaceReflectZ v) := by
  apply TranslationPeriod.transport
    (show Function.Surjective spaceReflectZ from
      fun p => ⟨spaceReflectZ p, by simp [spaceReflectZ]⟩)
    R.mem_spaceReflectZ_iff hv
  intro p
  ext <;> simp [spaceReflectZ, add_comm]

lemma checkerboard_power (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (hz : |HeightLift.height q + Real.pi| ≤ Real.pi / 2) :
    (R.horizontalComplex q ^ k).re ≤ 0 := by
  obtain ⟨j, r, θ, hr, hθ, hx, hy⟩ := R.checkerboard_closed_slab q hz
  have he : R.horizontalComplex q = (r : ℂ) * Complex.exp ((θ : ℂ) * I) := by
    apply Complex.ext
    · rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
      simpa [horizontalComplex] using hx
    · rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
      simpa [horizontalComplex] using hy
  rw [he]
  exact checkerboard_power_nonpos hr hθ

lemma axis_center_mem : ((0 : ℂ), Real.pi / 2) ∈ R.spaceImage := by
  obtain ⟨q, ha, hh⟩ := R.exists_axis_center
  refine ⟨q, Prod.ext ?_ hh⟩
  simp [spaceImmersion, horizontalComplex, ha.1, ha.2]

/-- There is no nonzero horizontal translation preserving the EW image. -/
theorem horizontal_period_zero {v : ℂ}
    (hv : TranslationPeriod R.spaceImage (v, 0)) : v = 0 := by
  let P : AddSubgroup ℂ := {
    carrier := {z | TranslationPeriod R.spaceImage (z, 0)}
    zero_mem' := by
      intro p
      change p + (0 : SpacePoint) ∈ R.spaceImage ↔ p ∈ R.spaceImage
      rw [add_zero]
    add_mem' := by intro x y hx hy; simpa using hx.add hy
    neg_mem' := by intro x hx; simpa using hx.neg }
  apply horizontal_period_obstruction h.out P ?_ ?_ v hv
  · intro z hz
    have hp : (z, Real.pi / 2) ∈ R.spaceImage := by
      have hh := (hz ((0 : ℂ), Real.pi / 2)).mpr R.axis_center_mem
      simpa using hh
    obtain ⟨q, hq⟩ := hp
    have hh := congrArg Prod.snd hq
    have hx := congrArg Prod.fst hq
    have hb := R.checkerboard_power q (by
      rw [show HeightLift.height q + Real.pi = Real.pi / 2 from hh]
      rw [abs_of_nonneg (by positivity)])
    change R.horizontalComplex q = z at hx
    rwa [hx] at hb
  · intro z hz
    exact R.period_screw hz

/-- Every ambient translation period is parallel to the vertical axis. -/
theorem period_vertical {v : SpacePoint} (hv : TranslationPeriod R.spaceImage v) : v.1 = 0 := by
  have hh := hv.add (R.period_reflectZ hv)
  have he : v + spaceReflectZ v = (v.1 + v.1, 0) := by ext <;> simp [spaceReflectZ]
  rw [he] at hh
  have hz := R.horizontal_period_zero hh
  exact (add_self_eq_zero.mp hz)

end KsIndex.KarcherData.PaperHalfPeriodRealization
