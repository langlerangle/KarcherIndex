module

public import KsIndexLean.KarcherDiskRotation

@[expose] public section


/-! Canonical encoding intertwines actual rotation and the disk-family action. -/
noncomputable section
open scoped ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

lemma diskRotation_coordinate_rotUnit (R : PaperHalfPeriodRealization k)
    (w : PuncturedClosedDisk k) :
    (R.diskRotation w).val.val = (SurfaceSym.rotUnit k : ℂ) * w.val.val := by
  have ha : (-2 * Real.pi / k : ℝ) = -(2 * Real.pi) / k := by ring
  simpa only [SurfaceSym.rotUnit, Circle.coe_exp, ha] using R.diskRotation_coordinate w

lemma encode_rotation_pullback (R : PaperHalfPeriodRealization k)
    {m : ℕ} [NeZero m]
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) :
    encodeDiskFunction (R.diskFunctionPullback (f ∘ R.periodRotation m)) =
      SurfaceSym.rotF (SurfaceSym.rotUnit k : ℂ) (encodeDiskFunction (R.diskFunctionPullback f)) := by
  have hk := SurfaceSym.rotUnit_pow (show 0 < k by have := h.out; omega)
  have hp : (SurfaceSym.rotUnit k : ℂ) ^ (2*k) = 1 := by
    rw [two_mul, pow_add, hk, one_mul]
  funext n z
  have hv : ((SurfaceSym.rotUnit k : ℂ) * z ∉ Surface.punctures k ∧
      ‖(SurfaceSym.rotUnit k : ℂ) * z‖ ≤ 1) ↔ (z ∉ Surface.punctures k ∧ ‖z‖ ≤ 1) := by
    simp only [Surface.punctures, Set.mem_ofPred_eq, mul_pow, hp, one_mul,
      norm_mul, Circle.norm_coe]
  by_cases hz : z ∉ Surface.punctures k ∧ ‖z‖ ≤ 1
  · let w : PuncturedClosedDisk k := ⟨⟨z,hz.1⟩,hz.2⟩
    change encodeDiskFunction _ n w.val.val =
      encodeDiskFunction _ n ((SurfaceSym.rotUnit k : ℂ) * w.val.val)
    rw [← R.diskRotation_coordinate_rotUnit w, encodeDiskFunction_on_disk,
      encodeDiskFunction_on_disk]
    change f (R.periodRotation m (R.orderedDiskPoint n w)) =
      f (R.orderedDiskPoint n (R.diskRotation w))
    rw [R.periodRotation_orderedDiskPoint]
  · have hz' := mt hv.mp hz
    simp only [SurfaceSym.rotF, encodeDiskFunction, dite_eq_right hz, dite_eq_right hz']


lemma compactSmooth_rotation_pullback (R : PaperHalfPeriodRealization k)
    {m : ℕ} [NeZero m]
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) :
    letI := HeightLift.periodChartedSpace R.hC m
    (ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f ∧ HasCompactSupport f) →
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (f ∘ R.periodRotation m) ∧
        HasCompactSupport (f ∘ R.periodRotation m) := by
  intro hf
  apply (R.compactSmooth_iff_encoding_mem_CcSmooth _).mpr
  rw [R.encode_rotation_pullback]
  exact SurfaceSym.rotF_mem_CcSmooth (Circle.norm_coe _)
    (SurfaceSym.rotUnit_pow (show 0 < k by have := h.out; omega))
    ((R.compactSmooth_iff_encoding_mem_CcSmooth f).mp hf)

end KsIndex.KarcherData.PaperHalfPeriodRealization
