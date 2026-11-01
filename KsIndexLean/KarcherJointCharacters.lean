module

public import KsIndexLean.KarcherRotationEncoding

@[expose] public section


/-! Canonical encoding identifies simultaneous translation and rotation
character conditions on actual compact smooth functions. -/
noncomputable section
open scoped ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

lemma encoding_scalar_relation_iff (R : PaperHalfPeriodRealization k)
    (f g : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (c : ℂ) :
    (∀ q, f q = c * g q) ↔ ∀ n z,
      encodeDiskFunction (R.diskFunctionPullback f) n z =
        c * encodeDiskFunction (R.diskFunctionPullback g) n z := by
  constructor
  · intro hf n z
    by_cases hz : z ∉ Surface.punctures k ∧ ‖z‖ ≤ 1
    · let w : PuncturedClosedDisk k := ⟨⟨z,hz.1⟩,hz.2⟩
      change encodeDiskFunction _ n w.val.val = c * encodeDiskFunction _ n w.val.val
      rw [encodeDiskFunction_on_disk, encodeDiskFunction_on_disk]
      exact hf _
    · simp only [encodeDiskFunction, dite_eq_right hz, mul_zero]
  · intro hf q
    obtain ⟨p,rfl⟩ := R.orderedDiskPoint_surjective q
    have he := hf p.1 p.2.val.val
    rw [encodeDiskFunction_on_disk, encodeDiskFunction_on_disk] at he
    exact he

lemma rotation_eigenvalue_iff (R : PaperHalfPeriodRealization k)
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (c : ℂ) :
    (∀ q, f (R.periodRotation m q) = c * f q) ↔ ∀ n z,
      SurfaceSym.rotF (SurfaceSym.rotUnit k : ℂ)
        (encodeDiskFunction (R.diskFunctionPullback f)) n z =
          c * encodeDiskFunction (R.diskFunctionPullback f) n z := by
  rw [← R.encode_rotation_pullback]
  exact R.encoding_scalar_relation_iff (f ∘ R.periodRotation m) f c

lemma compactSmooth_jointCharacters_iff (R : PaperHalfPeriodRealization k)
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (translationPhase rotationPhase : ℂ) :
    letI := HeightLift.periodChartedSpace R.hC m
    ((ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f ∧ HasCompactSupport f) ∧
      (∀ q, f (HeightLift.periodDeck m 1 q) = translationPhase * f q) ∧
      (∀ q, f (R.periodRotation m q) = rotationPhase * f q)) ↔
    (encodeDiskFunction (R.diskFunctionPullback f) ∈ Surface.CcSmooth k m ∧
      (∀ n z, SurfaceSym.shiftF (encodeDiskFunction (R.diskFunctionPullback f)) n z =
        translationPhase * encodeDiskFunction (R.diskFunctionPullback f) n z) ∧
      (∀ n z, SurfaceSym.rotF (SurfaceSym.rotUnit k : ℂ)
        (encodeDiskFunction (R.diskFunctionPullback f)) n z =
        rotationPhase * encodeDiskFunction (R.diskFunctionPullback f) n z)) := by
  exact and_congr (R.compactSmooth_iff_encoding_mem_CcSmooth f)
    (and_congr (R.translation_eigenvalue_iff f translationPhase)
      (R.rotation_eigenvalue_iff f rotationPhase))

end KsIndex.KarcherData.PaperHalfPeriodRealization
