module

public import KsIndexLean.KarcherSymmetryInverses
public import KsIndexLean.ProperFiniteReduction

@[expose] public section


/-! Compact inverse images in one fundamental height slab. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open Set
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- Horizontal multiplication by the inverse phase in product coordinates. -/
def ambientRotate (a : ℂ) (v : AmbientTriple) : AmbientTriple :=
  ((a⁻¹ * ((v.1 : ℂ) + (v.2.1 : ℂ) * Complex.I)).re,
   (a⁻¹ * ((v.1 : ℂ) + (v.2.1 : ℂ) * Complex.I)).im, v.2.2)

lemma continuous_ambientRotate (a : ℂ) : Continuous (ambientRotate a) := by
  unfold ambientRotate
  fun_prop

lemma rotationIterate_ambient (R : PaperHalfPeriodRealization k) (n : ℕ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    centeredLiftAmbient R.C R.t (R.rotationLift^[n] q) =
      (ambientRotate (Complex.exp ((-2 * Real.pi / k : ℝ) * Complex.I)))^[n]
        (centeredLiftAmbient R.C R.t q) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', R.rotationLift_ambient, ih,
      Function.iterate_succ_apply']
    rfl

lemma upperHalfSlab_rotation_cover (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (hz : HeightLift.height q + Real.pi ∈ Icc (Real.pi / 2) Real.pi) :
    ∃ n : Fin k, R.rotationLift^[n.val] q ∈ R.doubleSector := by
  have hh : HeightLift.height q + Real.pi ∈ Icc 0 Real.pi :=
    ⟨by linarith [hz.1, Real.pi_pos], hz.2⟩
  let w := (R.diskMap ⟨q, hh⟩).val
  have hq : HeightLift.projection q = finiteParameter w := (R.projection_agrees ⟨q, hh⟩).symm
  obtain ⟨n, hn, ha⟩ := exists_rotation_into_wedge h.out
    (R.powered_re_nonneg_of_upper_height q w hq hz)
  obtain ⟨v, hv, he, hnorm⟩ := R.rotationIterate_finite n q w hq
  refine ⟨⟨n, hn⟩, R.mem_doubleSector_of_arg _ v hv ?_ ?_ ?_ ?_⟩
  · simpa only [R.rotationIterate_height] using hh
  · exact hnorm.trans_le (R.diskMap ⟨q, hh⟩).property
  · rw [he]; exact ha.1
  · rw [he]; exact ha.2

lemma compact_doubleSector (R : PaperHalfPeriodRealization k) {K : Set AmbientTriple}
    (hK : IsCompact K) :
    IsCompact (R.doubleSector ∩ centeredLiftAmbient R.C R.t ⁻¹' K) := by
  have hc := (R.isProperMap_doubleSector.isCompact_preimage hK).image continuous_subtype_val
  convert hc using 1
  ext q
  simp only [mem_inter_iff, mem_preimage, mem_image, Subtype.exists, exists_and_right]
  aesop

lemma compact_upperHalfSlab (R : PaperHalfPeriodRealization k) {K : Set AmbientTriple}
    (hK : IsCompact K) :
    IsCompact ({q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C |
        HeightLift.height q + Real.pi ∈ Icc (Real.pi / 2) Real.pi} ∩
      centeredLiftAmbient R.C R.t ⁻¹' K) := by
  apply isCompact_restrict_of_finite_reductions R.continuous_centeredAmbient
    (isClosed_Icc.preimage (HeightLift.continuous_height.add continuous_const))
    (fun _ hK => R.compact_doubleSector hK)
    (fun n : Fin k => R.rotationLift^[n.val])
    (fun n : Fin k => R.rotationLift^[k - n.val])
    (fun n : Fin k => (ambientRotate (Complex.exp ((-2 * Real.pi / k : ℝ) * Complex.I)))^[n.val])
    (fun _ => R.continuous_rotationLift.iterate _)
    (fun _ => (continuous_ambientRotate _).iterate _)
    (fun n q => R.rotationIterate_undo (Nat.le_of_lt n.isLt) q)
    (fun n q => R.rotationIterate_ambient n.val q)
    (fun q hq => R.upperHalfSlab_rotation_cover q hq) hK

/-- The middle-height reflection is a screw after reflection in the lower seam. -/
def middleLift (R : PaperHalfPeriodRealization k) :=
  fun q => R.screwLift (lowerSeamLift R.C R.hC q)

lemma middleLift_height (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    HeightLift.height (R.middleLift q) + Real.pi =
      Real.pi - (HeightLift.height q + Real.pi) := by
  dsimp [middleLift]
  rw [R.screwLift_height]
  have ht := lowerSeamLift_height R.C R.hC q
  linarith

lemma compact_halfSlab (R : PaperHalfPeriodRealization k) {K : Set AmbientTriple}
    (hK : IsCompact K) :
    IsCompact ({q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C |
        HeightLift.height q + Real.pi ∈ Icc 0 Real.pi} ∩
      centeredLiftAmbient R.C R.t ⁻¹' K) := by
  let r := fun q => lowerSeamLift R.C R.hC (R.screwLiftInverse q)
  let A := fun v : AmbientTriple =>
    ((ambientRotate (Complex.exp ((-Real.pi / k : ℝ) * Complex.I)) v).1,
     (ambientRotate (Complex.exp ((-Real.pi / k : ℝ) * Complex.I)) v).2.1,
     Real.pi - v.2.2)
  apply isCompact_restrict_of_two_reductions R.continuous_centeredAmbient
    (isClosed_Icc.preimage (HeightLift.continuous_height.add continuous_const))
    (fun _ hK => R.compact_upperHalfSlab hK) R.middleLift r A
    ((continuous_lowerSeamLift R.C R.hC).comp R.continuous_screwLiftInverse)
    (by dsimp [A]; fun_prop) ?_ ?_ ?_ hK
  · intro q
    dsimp [r, middleLift]
    rw [R.screwLiftInverse_left, lowerSeamLift_involutive R.C R.hC]
  · intro q
    dsimp [middleLift]
    rw [R.screwLift_ambient, centeredLiftAmbient_lowerSeam]
    dsimp [A, ambientRotate, PeriodTarget.rotate, projectPeriod]
    congr 2; ring
  · intro q hq
    change HeightLift.height q + Real.pi ∈ Icc 0 Real.pi at hq
    by_cases hz : Real.pi / 2 ≤ HeightLift.height q + Real.pi
    · exact Or.inl ⟨hz, hq.2⟩
    · right
      change HeightLift.height (R.middleLift q) + Real.pi ∈ Icc _ _
      rw [R.middleLift_height]
      constructor <;> linarith [hq.1]

lemma compact_periodSlab (R : PaperHalfPeriodRealization k) {K : Set AmbientTriple}
    (hK : IsCompact K) :
    IsCompact ({q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C |
        HeightLift.height q + Real.pi ∈ Icc 0 (2 * Real.pi)} ∩
      centeredLiftAmbient R.C R.t ⁻¹' K) := by
  apply isCompact_restrict_of_two_reductions R.continuous_centeredAmbient
    (isClosed_Icc.preimage (HeightLift.continuous_height.add continuous_const))
    (fun _ hK => R.compact_halfSlab hK)
    (upperSeamLift R.C R.hC) (upperSeamLift R.C R.hC)
    (fun v : AmbientTriple => (v.1, v.2.1, 2 * Real.pi - v.2.2))
    (continuous_upperSeamLift R.C R.hC) (by fun_prop)
    (upperSeamLift_involutive R.C R.hC)
    (fun q => centeredLiftAmbient_upperSeam R.C R.hC R.t q) ?_ hK
  intro q hq
  change HeightLift.height q + Real.pi ∈ Icc 0 (2 * Real.pi) at hq
  by_cases hz : HeightLift.height q + Real.pi ≤ Real.pi
  · exact Or.inl ⟨hq.1, hz⟩
  · right
    change HeightLift.height (upperSeamLift R.C R.hC q) + Real.pi ∈ Icc _ _
    rw [upperSeamLift_height]
    constructor <;> linarith [hq.2]

end KsIndex.KarcherData.PaperHalfPeriodRealization
