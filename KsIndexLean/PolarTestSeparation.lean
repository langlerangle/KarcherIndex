module

public import KsIndexLean.PolarPairingIdentity
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

@[expose] public section


open Set MeasureTheory
open scoped ContDiff InnerProductSpace

noncomputable section
namespace KsIndex.Trace

/-- Circle restrictions of globally smooth complex functions. -/
def smoothCircleAlgebra : StarSubalgebra ℂ C(Circle₁, ℂ) where
  carrier := {f | ∃ H : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) H ∧ ∀ w : Circle₁, H w = f w}
  zero_mem' := ⟨fun _ => 0, contDiff_const, fun _ => rfl⟩
  add_mem' := by
    rintro f g ⟨H, hH, he⟩ ⟨K, hK, hk⟩
    exact ⟨fun z => H z + K z, hH.add hK, fun w => by simp [he w, hk w]⟩
  one_mem' := ⟨fun _ => 1, contDiff_const, fun _ => rfl⟩
  mul_mem' := by
    rintro f g ⟨H, hH, he⟩ ⟨K, hK, hk⟩
    exact ⟨fun z => H z * K z, hH.mul hK, fun w => by simp [he w, hk w]⟩
  algebraMap_mem' c := ⟨fun _ => c, contDiff_const, fun _ => rfl⟩
  star_mem' := by
    rintro f ⟨H, hH, he⟩
    exact ⟨fun z => star (H z), Complex.conjCLE.contDiff.comp hH,
      fun w => by simp [he w]⟩

lemma smoothCircleAlgebra_dense : Dense (smoothCircleAlgebra : Set C(Circle₁, ℂ)) := by
  have hs : smoothCircleAlgebra.SeparatesPoints := by
    intro x y hxy
    refine ⟨fun w => (w : ℂ), ?_, ?_⟩
    · exact ⟨⟨fun w => (w : ℂ), continuous_subtype_val⟩,
        ⟨id, contDiff_id, fun _ => rfl⟩, rfl⟩
    · exact fun h => hxy (Subtype.ext h)
  have h := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    smoothCircleAlgebra hs
  rw [dense_iff_closure_eq, ← StarSubalgebra.topologicalClosure_coe, h]
  rfl

/-- Smooth circle restrictions separate the actual complex L² space. -/
theorem smoothCircle_tests_separate (d : Lp ℂ 2 circleMeasure)
    (hd : ∀ f ∈ smoothCircleAlgebra,
      inner ℂ (ContinuousMap.toLp 2 circleMeasure ℂ f) d = 0) : d = 0 := by
  have hall : ∀ f : C(Circle₁, ℂ),
      inner ℂ (ContinuousMap.toLp 2 circleMeasure ℂ f) d = 0 := by
    intro f
    exact smoothCircleAlgebra_dense.induction hd
      (isClosed_eq ((ContinuousMap.toLp 2 circleMeasure ℂ).continuous.inner continuous_const)
        continuous_const) f
  have hlp : ∀ f : Lp ℂ 2 circleMeasure, inner ℂ f d = 0 := by
    intro f
    exact (ContinuousMap.toLp_denseRange (p := 2) ℂ circleMeasure ℂ (by norm_num)).induction_on f
      (isClosed_eq (continuous_id.inner continuous_const) continuous_const) hall
  exact inner_self_eq_zero.mp (hlp d)

end KsIndex.Trace
