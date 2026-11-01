module

public import KsIndexLean.SeamTraceNormalization
public import KsIndexLean.SurfaceSym

@[expose] public section


/-! Trace normalization commutes with translation and root-of-unity rotation. -/
noncomputable section
namespace KsIndex.FaithfulInjection
open Surface SurfaceSym
variable {k m : ℕ}

lemma testTrace_shift (u : ZMod (2*m) → ℂ → ℂ) :
    testTrace k m (shiftF u) = shiftF (testTrace k m u) := by
  funext n w
  have hn : (n+2-1 : ZMod (2*m)) = (n-1)+2 := by ring
  simp only [testTrace, shiftF]
  rw [seamArc_add_two k m n, hn, seamArc_add_two k m (n-1)]

lemma testTrace_rotation (u : ZMod (2*m) → ℂ → ℂ) {a : ℂ}
    (ha : ‖a‖ = 1) (hak : a ^ k = 1) :
    testTrace k m (rotF a u) = rotF a (testTrace k m u) := by
  funext n w
  have hn : ‖a*w‖ = ‖w‖ := by rw [norm_mul, ha, one_mul]
  have hs : ∀ i : ZMod (2*m), a*w ∈ seamArc k m i ↔ w ∈ seamArc k m i := by
    intro i
    simp only [seamArc, arc, Set.mem_ofPred_eq, hn, mul_pow, hak, one_mul]
  simp only [testTrace, rotF]
  rw [hn, hs n, hs (n-1)]

lemma testTrace_shift_character (u : ZMod (2*m) → ℂ → ℂ) (c : ℂ)
    (hu : ∀ n w, shiftF u n w = c * u n w) :
    ∀ n w, shiftF (testTrace k m u) n w = c * testTrace k m u n w := by
  have he : shiftF u = c • u := funext fun n => funext fun w => hu n w
  rw [← testTrace_shift, he]
  have hm := (testTraceLinear k m).map_smul c u
  intro n w
  exact congrFun (congrFun hm n) w

lemma testTrace_rotation_character (u : ZMod (2*m) → ℂ → ℂ) {a : ℂ}
    (ha : ‖a‖ = 1) (hak : a ^ k = 1) (c : ℂ)
    (hu : ∀ n w, rotF a u n w = c * u n w) :
    ∀ n w, rotF a (testTrace k m u) n w = c * testTrace k m u n w := by
  have he : rotF a u = c • u := funext fun n => funext fun w => hu n w
  rw [← testTrace_rotation u ha hak, he]
  have hm := (testTraceLinear k m).map_smul c u
  intro n w
  exact congrFun (congrFun hm n) w

end KsIndex.FaithfulInjection
