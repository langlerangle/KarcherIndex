module

/-
Propagation of an almost-everywhere puncture hole through a joined disk extension.

If `f` vanishes almost everywhere near a unit-circle point inside the open disk,
`joined_puncture_hole` gives a smaller whole-plane neighborhood on which the
extension `joined f s` vanishes almost everywhere. The scalar `s : ℂ` is arbitrary;
no continuity or smoothness hypothesis on `f` is required.

The proof uses inversion away from the origin, preservation of null sets under
that differentiable map, and the nullity of the unit circle. It yields an
almost-everywhere conclusion, not pointwise vanishing on the seam.

Proof contribution: Harmonic's Aristotle, submitted by Astra on 2026-09-16 and
ported by Kai on 2026-09-18. The returned development used Lean 4.28.0 and
Mathlib revision 8f9d9cff; the repository's current toolchain is specified separately.
-/
public import Mathlib

@[expose] public section

open Set MeasureTheory
noncomputable section
namespace AstraAristotle
/-- Same formula as KsIndex.Trace.radialInversion. -/
def inversion (z : ℂ) : ℂ := (‖z‖ ^ 2)⁻¹ • z
/-- Same formula as joinedDiskValue when its two disk inputs coincide. -/
def joined (f : ℂ → ℂ) (s : ℂ) (z : ℂ) : ℂ :=
  if ‖z‖ ≤ 1 then f z else s • f (inversion z)

/-- The explicit radial inversion agrees with `z ↦ 1 / conj z` away from the origin. -/
lemma inversion_eq_inv_conj {z : ℂ} (hz : z ≠ 0) : inversion z = ((starRingEnd ℂ) z)⁻¹ := by
  have h : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hz' : (starRingEnd ℂ) z ≠ 0 := by simpa using hz
  rw [inversion, Complex.real_smul, Complex.ofReal_inv, h]
  field_simp

lemma norm_inversion (z : ℂ) : ‖inversion z‖ = ‖z‖⁻¹ := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [inversion]
  · have hz' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    rw [inversion, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg ‖z‖), sq]
    field_simp

lemma inversion_ne_zero {z : ℂ} (hz : z ≠ 0) : inversion z ≠ 0 := by
  simp [inversion, hz]

/-- Inversion is an involution away from the origin. -/
lemma inversion_inversion {z : ℂ} (hz : z ≠ 0) : inversion (inversion z) = z := by
  rw [inversion_eq_inv_conj (inversion_ne_zero hz), inversion_eq_inv_conj hz]
  simp

/-- Inversion is (real-)differentiable away from the origin, hence locally continuous there. -/
lemma differentiableAt_inversion {z : ℂ} (hz : z ≠ 0) : DifferentiableAt ℝ inversion z := by
  have h : ∀ᶠ w in nhds z, inversion w = ((starRingEnd ℂ) w)⁻¹ := by
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw using inversion_eq_inv_conj hw
  have hc : DifferentiableAt ℝ (fun w : ℂ => (starRingEnd ℂ) w) z :=
    Complex.conjCLE.differentiableAt
  have hinv : DifferentiableAt ℂ (fun w : ℂ => w⁻¹) ((starRingEnd ℂ) z) :=
    differentiableAt_inv (by simpa using hz)
  exact ((hinv.restrictScalars ℝ).comp z hc).congr_of_eventuallyEq h

/-- Inversion maps null sets away from the origin to null sets. -/
lemma volume_image_inversion_eq_zero {E : Set ℂ} (hE : volume E = 0)
    (h0 : (0 : ℂ) ∉ E) : volume (inversion '' E) = 0 := by
  refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ hE
  intro w hw
  exact (differentiableAt_inversion (by rintro rfl; exact h0 hw)).differentiableWithinAt

/-- Quantitative continuity of inversion at a point of the unit circle, from outside. -/
lemma dist_inversion_lt {z p : ℂ} (hp : ‖p‖ = 1) (hz : 1 < ‖z‖) {r : ℝ}
    (hzp : dist z p < r) : dist (inversion z) p < 3 * r := by
  set t : ℝ := ‖z‖ with ht
  have ht0 : (0 : ℝ) < t := lt_trans one_pos hz
  have htr : t - 1 < r := by
    have : t - ‖p‖ ≤ ‖z - p‖ := norm_sub_norm_le z p
    rw [hp] at this
    rw [dist_eq_norm] at hzp
    linarith
  have hsub : inversion z - z = ((t ^ 2)⁻¹ - 1) • z := by
    rw [inversion, sub_smul, one_smul, ht]
  have hnorm : ‖inversion z - z‖ = |(t ^ 2)⁻¹ - 1| * t := by
    rw [hsub, norm_smul, Real.norm_eq_abs, ht]
  have habs : |(t ^ 2)⁻¹ - 1| = 1 - (t ^ 2)⁻¹ := by
    have h1 : (t ^ 2)⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]
      right
      nlinarith
    rw [abs_of_nonpos (by linarith)]
    ring
  have key : (1 - (t ^ 2)⁻¹) * t < 2 * r := by
    have hexp : (1 - (t ^ 2)⁻¹) * t = t - t⁻¹ := by
      field_simp
    rw [hexp]
    have hinv : t⁻¹ * t = 1 := inv_mul_cancel₀ (ne_of_gt ht0)
    nlinarith [mul_pos ht0 (sub_pos.mpr hz), sq_nonneg (t - 1), inv_pos.mpr ht0]
  calc dist (inversion z) p ≤ dist (inversion z) z + dist z p := dist_triangle _ _ _
    _ = ‖inversion z - z‖ + dist z p := by rw [dist_eq_norm]
    _ < 2 * r + r := by rw [hnorm, habs]; linarith
    _ = 3 * r := by ring

/-- Transfer an AE disk puncture hole to the genuine joined extension. -/
theorem joined_puncture_hole (f : ℂ → ℂ) (s p : ℂ) (hp : ‖p‖ = 1)
    {R : ℝ} (hR : 0 < R)
    (hf : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) 1),
      dist z p < R → f z = 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ᵐ z ∂(volume : Measure ℂ),
      dist z p < r → joined f s z = 0 := by
  classical
  -- the bad set inside the unit disk is null
  set A : Set ℂ := {z : ℂ | dist z p < R ∧ f z ≠ 0} ∩ Metric.ball (0 : ℂ) 1 with hAdef
  have hA : volume A = 0 := by
    rw [ae_iff, Measure.restrict_apply' measurableSet_ball] at hf
    have : {z : ℂ | ¬(dist z p < R → f z = 0)} ∩ Metric.ball (0 : ℂ) 1 = A := by
      ext z; simp [hAdef]
    rwa [this] at hf
  set r : ℝ := min (R / 3) 1 with hrdef
  have hr0 : 0 < r := lt_min (by linarith) one_pos
  have hrR : 3 * r ≤ R := by
    have : r ≤ R / 3 := min_le_left _ _
    linarith
  have hr1 : r ≤ 1 := min_le_right _ _
  refine ⟨r, hr0, ?_⟩
  rw [ae_iff]
  -- the bad set of the conclusion sits inside three null sets
  set B : Set ℂ := A ∩ {w : ℂ | (1 : ℝ) / 2 ≤ ‖w‖} with hBdef
  refine measure_mono_null
    (t := A ∪ Metric.sphere (0 : ℂ) 1 ∪ inversion '' B) ?_ ?_
  · intro z hz
    simp only [mem_setOf_eq, Classical.not_imp] at hz
    obtain ⟨hzr, hzj⟩ := hz
    rcases lt_trichotomy ‖z‖ 1 with h | h | h
    · refine Or.inl (Or.inl ⟨⟨lt_of_lt_of_le hzr (by linarith), ?_⟩, ?_⟩)
      · simpa [joined, le_of_lt h] using hzj
      · simpa [Metric.mem_ball] using h
    · exact Or.inl (Or.inr (by simp [h]))
    · -- exterior point: use the inversion
      have hz0 : z ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at h
        linarith
      have hznorm : ‖z‖ < 2 := by
        have : ‖z‖ - ‖p‖ ≤ ‖z - p‖ := norm_sub_norm_le z p
        rw [hp] at this
        rw [dist_eq_norm] at hzr
        linarith
      have hw : dist (inversion z) p < R :=
        lt_of_lt_of_le (dist_inversion_lt hp h hzr) hrR
      have hwball : inversion z ∈ Metric.ball (0 : ℂ) 1 := by
        have : ‖inversion z‖ = ‖z‖⁻¹ := norm_inversion z
        simp only [Metric.mem_ball, dist_zero_right, this]
        rw [inv_lt_one_iff₀]
        exact Or.inr h
      have hfw : f (inversion z) ≠ 0 := by
        intro h0
        apply hzj
        simp [joined, not_le.mpr h, h0]
      have hwhalf : (1 : ℝ) / 2 ≤ ‖inversion z‖ := by
        rw [norm_inversion z]
        rw [le_inv_comm₀ (by norm_num) (lt_trans one_pos h)]
        linarith
      exact Or.inr ⟨inversion z, ⟨⟨⟨hw, hfw⟩, hwball⟩, hwhalf⟩, inversion_inversion hz0⟩
  · refine measure_union_null (measure_union_null hA (Measure.addHaar_sphere _ _ _)) ?_
    refine volume_image_inversion_eq_zero (measure_mono_null inter_subset_left hA) ?_
    intro h0
    have := h0.2
    norm_num at this
end AstraAristotle
