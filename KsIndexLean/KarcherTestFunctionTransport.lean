module

public import KsIndexLean.KarcherSmoothFunctionTransport
public import KsIndexLean.SeamTraceNormalization

@[expose] public section


/-! Linear descent of raw model test functions to the actual EW quotient.
Receiving-seam redundancy is normalized without changing the model form. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold
namespace KsIndex.KarcherData
open scoped ParameterAtlas
open FaithfulInjection
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

lemma testTrace_punctureZero (u : ZMod (2*m) → ℂ → ℂ) :
    Surface.PunctureZero k (testTrace k m u) := by
  intro n w hw
  exact testTrace_puncture u n (puncture_norm h.out hw) hw

/-- Normalize seam values, then restrict to the genuine punctured disks. -/
def normalizedDiskFamily :
    (ZMod (2*m) → ℂ → ℂ) →ₗ[ℂ] CompatibleDiskFunctions k m where
  toFun u := restrictSeamFamily (testTrace k m u) (testTrace_seamVal u)
  map_add' := by
    intro u v
    apply Subtype.ext
    funext p
    exact congrFun (congrFun ((testTraceLinear k m).map_add u v) p.1) p.2.val.val
  map_smul' := by
    intro c u
    apply Subtype.ext
    funext p
    exact congrFun (congrFun ((testTraceLinear k m).map_smul c u) p.1) p.2.val.val

lemma encode_normalizedDiskFamily (u : ZMod (2*m) → ℂ → ℂ) :
    encodeDiskFunction (normalizedDiskFamily (k := k) u) = testTrace k m u :=
  encode_restrictSeamFamily _ (testTrace_seamVal u) (testTrace_punctureZero u)
    (fun n w hw => testTrace_exterior u n hw)

lemma normalizedDiskFamily_encode (u : CompatibleDiskFunctions k m) :
    normalizedDiskFamily (encodeDiskFunction u) = u := by
  have he := testTrace_eq_self (encodeDiskFunction u) (encodeDiskFunction_seamVal u)
    (encodeDiskFunction_punctureZero u) (encodeDiskFunction_exterior u)
  apply Subtype.ext
  funext p
  change testTrace k m (encodeDiskFunction u) p.1 p.2.val.val = u.val p
  rw [he, encodeDiskFunction_on_disk]

namespace PaperHalfPeriodRealization

/-- Descend the trace-normalized representative. This map need not be injective
on arbitrary raw families: receiving-seam spikes are deliberately discarded. -/
def modelTestFunction (R : PaperHalfPeriodRealization k) :
    (ZMod (2*m) → ℂ → ℂ) →ₗ[ℂ]
      (HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) :=
  (R.diskFunctionEquiv (m := m)).symm.toLinearMap.comp normalizedDiskFamily

lemma modelTestFunction_encoding (R : PaperHalfPeriodRealization k)
    (u : ZMod (2*m) → ℂ → ℂ) :
    encodeDiskFunction (R.diskFunctionPullback (R.modelTestFunction u)) = testTrace k m u := by
  change encodeDiskFunction (R.diskFunctionEquiv ((R.diskFunctionEquiv).symm
    (normalizedDiskFamily u))) = _
  rw [LinearEquiv.apply_symm_apply, encode_normalizedDiskFamily]

lemma modelTestFunction_compactSmooth (R : PaperHalfPeriodRealization k)
    (u : Surface.CcSmooth k m) :
    letI := HeightLift.periodChartedSpace R.hC m
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (R.modelTestFunction u.val) ∧
      HasCompactSupport (R.modelTestFunction u.val) := by
  apply (R.compactSmooth_iff_encoding_mem_CcSmooth _).mpr
  rw [R.modelTestFunction_encoding]
  exact testTrace_mem_CcSmooth u.property

/-- Descent preserves the original model quadratic form on canonical encoding.
Identification with the intrinsic geometric form is a separate metric theorem. -/
lemma modelTestFunction_modelForm (R : PaperHalfPeriodRealization k)
    (u : ZMod (2*m) → ℂ → ℂ) :
    Surface.jacobiQ k m (encodeDiskFunction (R.diskFunctionPullback
      (R.modelTestFunction u))) = Surface.jacobiQ k m u := by
  rw [R.modelTestFunction_encoding, testTrace_jacobiQ]

/-- Canonical encoding is a right inverse to raw model descent. -/
lemma modelTestFunction_encoding_section (R : PaperHalfPeriodRealization k)
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) :
    R.modelTestFunction (encodeDiskFunction (R.diskFunctionPullback f)) = f := by
  change (R.diskFunctionEquiv).symm
    (normalizedDiskFamily (encodeDiskFunction (R.diskFunctionPullback f))) = f
  rw [normalizedDiskFamily_encode]
  exact (R.diskFunctionEquiv).symm_apply_apply f

lemma modelTestFunction_surjective_compactSmooth (R : PaperHalfPeriodRealization k)
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) :
    letI := HeightLift.periodChartedSpace R.hC m
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f → HasCompactSupport f →
      ∃ u : Surface.CcSmooth k m, R.modelTestFunction u.val = f := by
  intro hf hc
  exact ⟨⟨encodeDiskFunction (R.diskFunctionPullback f),
    (R.compactSmooth_iff_encoding_mem_CcSmooth f).mp ⟨hf,hc⟩⟩,
    R.modelTestFunction_encoding_section f⟩

end PaperHalfPeriodRealization
end KsIndex.KarcherData
