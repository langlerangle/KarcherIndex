module

public import KsIndexLean.SingleDisk

@[expose] public section


open Set Filter Topology
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.Bracket KsIndex.SingleDisk

/-- Smooth reflection averaging, used on collars away from the inversion singularity. -/
def reflectionAverage (s : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (f z + s * f (σ z)) / 2

lemma reflectionAverage_parity (s : ℂ) (hs : s ^ 2 = 1) (f : ℂ → ℂ) (z : ℂ) :
    s * reflectionAverage s f (σ z) = reflectionAverage s f z := by
  simp only [reflectionAverage, σ_σ]
  have hh : s * s = 1 := by simpa only [pow_two] using hs
  calc
    s * ((f (σ z) + s * f z) / 2) = (s * f (σ z) + (s * s) * f z) / 2 := by ring
    _ = (f z + s * f (σ z)) / 2 := by rw [hh]; ring

lemma reflectionAverage_fixed (s : ℂ) (f : ℂ → ℂ)
    (hf : ∀ z, s * f (σ z) = f z) : reflectionAverage s f = f := by
  funext z
  rw [reflectionAverage, hf]
  ring

lemma reflectionAverage_idempotent (s : ℂ) (hs : s ^ 2 = 1) (f : ℂ → ℂ) :
    reflectionAverage s (reflectionAverage s f) = reflectionAverage s f :=
  reflectionAverage_fixed s _ (reflectionAverage_parity s hs f)

lemma reflectionAverage_contDiffAt (s : ℂ) {f : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0)
    (hf : ContDiffAt ℝ ∞ f z) (hi : ContDiffAt ℝ ∞ f (σ z)) :
    ContDiffAt ℝ ∞ (reflectionAverage s f) z := by
  exact (hf.add (contDiffAt_const.mul (hi.comp z (contDiffAt_σ hz)))).div_const 2

/-- Keep the paper's raw disk convention: retain circle values, set exterior values to zero. -/
def closedDiskRestriction (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if ‖z‖ ≤ 1 then f z else 0

lemma refl_closedDiskRestriction_average (s : ℂ) (hs : s ^ 2 = 1) (f : ℂ → ℂ) :
    refl s (closedDiskRestriction (reflectionAverage s f)) = reflectionAverage s f := by
  funext z
  by_cases hz : ‖z‖ ≤ 1
  · simp only [KsIndex.SingleDisk.refl, closedDiskRestriction, ite_eq_left hz]
  · have hn : 0 < ‖z‖ := lt_trans zero_lt_one (lt_of_not_ge hz)
    have hi : ‖σ z‖ ≤ 1 := by
      rw [norm_σ]
      exact (inv_le_one₀ hn).mpr (le_of_lt (lt_of_not_ge hz))
    simp only [KsIndex.SingleDisk.refl, ite_eq_right hz, closedDiskRestriction, ite_eq_left hi]
    exact reflectionAverage_parity s hs f z

/-- The actual paper reflection is smooth across every nonzero point where both germs are smooth. -/
lemma refl_average_contDiffAt (s : ℂ) (hs : s ^ 2 = 1) {f : ℂ → ℂ} {z : ℂ}
    (hz : z ≠ 0) (hf : ContDiffAt ℝ ∞ f z) (hi : ContDiffAt ℝ ∞ f (σ z)) :
    ContDiffAt ℝ ∞ (refl s (closedDiskRestriction (reflectionAverage s f))) z := by
  rw [refl_closedDiskRestriction_average s hs]
  exact reflectionAverage_contDiffAt s hz hf hi

lemma closedDiskRestriction_oneSided {f : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ ∞ f z) : OneSided (closedDiskRestriction f) z := by
  refine ⟨f, hf, Eventually.of_forall fun w hw => ?_⟩
  exact ite_eq_left (KsIndex.SurfaceForm.mem_disk_iff.mp hw).le

lemma reflectionAverage_odd_circle (f : ℂ → ℂ) {z : ℂ} (hz : ‖z‖ = 1) :
    closedDiskRestriction (reflectionAverage (-1) f) z = 0 := by
  simp [closedDiskRestriction, hz, reflectionAverage, σ_self hz]

end KsIndex.Trace
