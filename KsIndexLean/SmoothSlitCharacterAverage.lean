module

public import KsIndexLean.WeakCharacterProjection
public import KsIndexLean.PuncturedSlitPairApproximation
public import KsIndexLean.D5CoreEquivariance

@[expose] public section


open Set MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.FormIndex KsIndex.SurfaceSym KsIndex.SingleDisk

/-- The pointwise finite rotation average corresponding to `carrierCharProj`. -/
def smoothCharacterAverage (k r : ℕ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (k : ℂ)⁻¹ * ∑ i ∈ Finset.range k, xi k ^ (r * i) * f ((rotUnit k : ℂ) ^ i * z)

lemma smoothCharacterAverage_smooth (k r : ℕ) {f : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (smoothCharacterAverage k r f) := by
  apply ContDiff.mul contDiff_const
  exact ContDiff.sum (fun i _ => contDiff_const.mul (hf.comp (contDiff_const.mul contDiff_id)))

lemma restricted_phase_smul (c d : ℂ) (f g : ℂ → ℂ) :
    phaseGerm c (closedDiskRestriction (fun z => d * f z))
      (closedDiskRestriction (fun z => d * g z)) =
      fun z => d * phaseGerm c (closedDiskRestriction f) (closedDiskRestriction g) z := by
  funext z
  simp only [phaseGerm, closedDiskRestriction]
  split_ifs <;> ring

lemma restricted_phase_rotation {a : ℂ} (ha : ‖a‖ = 1) (c : ℂ) (f g : ℂ → ℂ) :
    phaseGerm c (closedDiskRestriction (fun z => f (a * z)))
      (closedDiskRestriction (fun z => g (a * z))) =
      fun z => phaseGerm c (closedDiskRestriction f) (closedDiskRestriction g) (a * z) := by
  funext z
  simp only [phaseGerm, closedDiskRestriction, norm_mul, ha, one_mul, σ_unimodular_mul ha]

lemma smoothCharacterAverage_phase (k r : ℕ) (c : ℂ) (f g : ℂ → ℂ) :
    phaseGerm c (closedDiskRestriction (smoothCharacterAverage k r f))
      (closedDiskRestriction (smoothCharacterAverage k r g)) =
      smoothCharacterAverage k r
        (phaseGerm c (closedDiskRestriction f) (closedDiskRestriction g)) := by
  unfold smoothCharacterAverage
  rw [restricted_phase_smul, restricted_phase_sum]
  funext z
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [restricted_phase_smul, restricted_phase_rotation (by simp)]

/-- Averaging preserves smooth gluing on each arc for any slit phase. -/
lemma smoothCharacterAverage_seam {k : ℕ} (hk : 0 < k) (r b : ℕ) (c : ℂ)
    {f g : ℂ → ℂ}
    (hs : ∀ z ∈ KsIndex.Surface.arc k b,
      ContDiffAt ℝ ∞ (phaseGerm c (closedDiskRestriction f) (closedDiskRestriction g)) z) :
    ∀ z ∈ KsIndex.Surface.arc k b,
      ContDiffAt ℝ ∞ (phaseGerm c
        (closedDiskRestriction (smoothCharacterAverage k r f))
        (closedDiskRestriction (smoothCharacterAverage k r g))) z := by
  intro z hz
  rw [smoothCharacterAverage_phase]
  apply ContDiffAt.mul contDiffAt_const
  apply ContDiffAt.sum
  intro i hi
  apply ContDiffAt.mul contDiffAt_const
  apply (hs _ (mul_mem_arc_same (by simp) ?_ hz)).comp z
    (contDiffAt_const.mul contDiffAt_id)
  rw [← pow_mul, Nat.mul_comm i k, pow_mul, KsIndex.SurfaceSym.rotUnit_pow hk, one_pow]

/-- Unimodular rotations preserve the radius of a puncture hole. -/
lemma smoothCharacterAverage_holes {k : ℕ} (hk : 0 < k) (r : ℕ) (f : ℂ → ℂ)
    {δ : ℝ} (hf : ∀ q ∈ KsIndex.Surface.punctures k, ∀ z, ‖z - q‖ < δ → f z = 0) :
    ∀ q ∈ KsIndex.Surface.punctures k, ∀ z, ‖z - q‖ < δ →
      smoothCharacterAverage k r f z = 0 := by
  intro q hq z hz
  unfold smoothCharacterAverage
  have he : ∀ i ∈ Finset.range k, f ((rotUnit k : ℂ) ^ i * z) = 0 := by
    intro i hi
    apply hf ((rotUnit k : ℂ) ^ i * q) (mul_mem_punctures_same ?_ hq)
    · simpa only [← mul_sub, norm_mul, norm_pow, Circle.norm_coe, one_pow, one_mul] using hz
    · rw [← pow_mul, Nat.mul_comm i k, pow_mul, KsIndex.SurfaceSym.rotUnit_pow hk, one_pow]
  rw [Finset.sum_eq_zero (fun i hi => by rw [he i hi, mul_zero]), mul_zero]

/-- The pointwise average represents the value of the continuous H1 average. -/
lemma smoothCharacterAverage_value (k r : ℕ) {f : ℂ → ℂ} {u : ComplexH1}
    (hf : (valueCLM u : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] f) :
    (valueCLM (carrierCharProj k r u) : ℂ → ℂ)
      =ᵐ[volume.restrict (disk : Set ℂ)] smoothCharacterAverage k r f := by
  have hrot i : (fun z => valueCLM u ((rotUnit k : ℂ) ^ i * z))
      =ᵐ[volume.restrict (disk : Set ℂ)] (fun z => f ((rotUnit k : ℂ) ^ i * z)) := by
    have h := (measurePreserving_planeRotation_disk
      ((i : ℝ) * rotAngle k)).quasiMeasurePreserving.ae hf
    filter_upwards [h] with z hz
    simpa only [planeRotation_rotAngle_pow] using hz
  have hall : ∀ᵐ z ∂volume.restrict (disk : Set ℂ), ∀ i ∈ Finset.range k,
      valueCLM u ((rotUnit k : ℂ) ^ i * z) = f ((rotUnit k : ℂ) ^ i * z) :=
    (eventually_all_finset _).mpr (fun i _ => hrot i)
  filter_upwards [carrierCharProj_value_ae k r u, hall] with z hz he
  rw [hz]
  simp only [smoothCharacterAverage, smul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl (fun i hi => by rw [he i hi])

end KsIndex.Trace
