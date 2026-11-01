module

public import KsIndexLean.KarcherJointCharacters
public import KsIndexLean.SeamTraceCharacters

@[expose] public section


/-! Raw compact smooth character sectors descend surjectively to the actual
EW quotient. Canonical encoding supplies a section, not a raw-family inverse. -/
noncomputable section
open scoped ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open FaithfulInjection
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

lemma modelTestFunction_jointCharacters (R : PaperHalfPeriodRealization k)
    (u : Surface.CcSmooth k m) (c d : ℂ)
    (ht : ∀ n w, SurfaceSym.shiftF u.val n w = c * u.val n w)
    (hr : ∀ n w, SurfaceSym.rotF (SurfaceSym.rotUnit k : ℂ) u.val n w = d * u.val n w) :
    (∀ q, R.modelTestFunction u.val (HeightLift.periodDeck m 1 q) =
      c * R.modelTestFunction u.val q) ∧
    (∀ q, R.modelTestFunction u.val (R.periodRotation m q) =
      d * R.modelTestFunction u.val q) := by
  constructor
  · apply (R.translation_eigenvalue_iff _ c).mpr
    rw [R.modelTestFunction_encoding]
    exact testTrace_shift_character u.val c ht
  · apply (R.rotation_eigenvalue_iff _ d).mpr
    rw [R.modelTestFunction_encoding]
    exact testTrace_rotation_character u.val (Circle.norm_coe _)
      (SurfaceSym.rotUnit_pow (show 0 < k by have := h.out; omega)) d hr

/-- Every actual compact smooth joint-character function has a raw model test
representative in the same sector, chosen by its canonical encoding. -/
lemma modelTestFunction_surjective_sector (R : PaperHalfPeriodRealization k)
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (c d : ℂ) :
    letI := HeightLift.periodChartedSpace R.hC m
    (ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f ∧ HasCompactSupport f) →
    (∀ q, f (HeightLift.periodDeck m 1 q) = c * f q) →
    (∀ q, f (R.periodRotation m q) = d * f q) →
    ∃ u : Surface.CcSmooth k m,
      (∀ n w, SurfaceSym.shiftF u.val n w = c * u.val n w) ∧
      (∀ n w, SurfaceSym.rotF (SurfaceSym.rotUnit k : ℂ) u.val n w = d * u.val n w) ∧
      R.modelTestFunction u.val = f := by
  intro hf ht hr
  have he := (R.compactSmooth_jointCharacters_iff f c d).mp ⟨hf,ht,hr⟩
  exact ⟨⟨encodeDiskFunction (R.diskFunctionPullback f),he.1⟩,
    he.2.1,he.2.2,R.modelTestFunction_encoding_section f⟩

/-- Exact sectorwise image of raw compact smooth descent. No injectivity on
redundant raw boundary data is asserted. -/
lemma compactSmooth_sector_iff_descent (R : PaperHalfPeriodRealization k)
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (c d : ℂ) :
    letI := HeightLift.periodChartedSpace R.hC m
    ((ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f ∧ HasCompactSupport f) ∧
      (∀ q, f (HeightLift.periodDeck m 1 q) = c * f q) ∧
      (∀ q, f (R.periodRotation m q) = d * f q)) ↔
    ∃ u : Surface.CcSmooth k m,
      (∀ n w, SurfaceSym.shiftF u.val n w = c * u.val n w) ∧
      (∀ n w, SurfaceSym.rotF (SurfaceSym.rotUnit k : ℂ) u.val n w = d * u.val n w) ∧
      R.modelTestFunction u.val = f := by
  constructor
  · rintro ⟨hf,ht,hr⟩
    exact R.modelTestFunction_surjective_sector f c d hf ht hr
  · rintro ⟨u,ht,hr,rfl⟩
    exact ⟨R.modelTestFunction_compactSmooth u,R.modelTestFunction_jointCharacters u c d ht hr⟩

end KsIndex.KarcherData.PaperHalfPeriodRealization
