module

public import KsIndexLean.KarcherTestFunctionTransport
public import KsIndexLean.SurfaceSym

@[expose] public section


/-! Actual positive full-period translation induces the paper's forward copy
shift. Pullback means precomposition by the positive action, not its inverse. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold
namespace KsIndex.KarcherData
namespace HeightLift
variable {P : Type*} {F : P → PeriodTarget}

/-- The actual deck translation descended to the m-period quotient. -/
def periodDeck (m : ℕ) (j : ℤ) : PeriodQuotient F m → PeriodQuotient F m :=
  Quotient.map (deck j) (by
    rintro q r ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    rw [← deck_add, ← deck_add, add_comm])

@[simp] lemma periodDeck_mk (m : ℕ) (j : ℤ) (q : HeightLift F) :
    periodDeck m j (periodQuotientMap m q) = periodQuotientMap m (deck j q) := rfl

lemma periodDeck_add (m : ℕ) (i j : ℤ) (q : PeriodQuotient F m) :
    periodDeck m (i+j) q = periodDeck m i (periodDeck m j q) := by
  induction q using Quotient.inductionOn with
  | h q => exact congrArg (periodQuotientMap m) (deck_add i j q)

@[simp] lemma periodDeck_zero (m : ℕ) (q : PeriodQuotient F m) : periodDeck m 0 q = q := by
  induction q using Quotient.inductionOn with
  | h q => exact congrArg (periodQuotientMap m) (deck_zero q)

lemma periodDeck_period (m : ℕ) (q : PeriodQuotient F m) : periodDeck m (m : ℤ) q = q := by
  induction q using Quotient.inductionOn with
  | h q =>
    apply Quotient.sound
    refine ⟨-1, ?_⟩
    rw [← deck_add]
    simp

variable [TopologicalSpace P]
lemma continuous_periodDeck (m : ℕ) (j : ℤ) : Continuous (periodDeck (F := F) m j) := by
  rw [(periodQuotientMap_isQuotientMap (F := F) m).continuous_iff]
  exact (periodQuotientMap_isQuotientMap (F := F) m).continuous.comp (deckHomeomorph j).continuous
end HeightLift

namespace PaperHalfPeriodRealization
open scoped ParameterAtlas
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

lemma periodDeck_evenPoint (R : PaperHalfPeriodRealization k) (i j : ℤ)
    (w : PuncturedClosedDisk k) :
    HeightLift.periodDeck m i (R.evenPeriodPoint m j w) = R.evenPeriodPoint m (i+j) w := by
  exact congrArg (HeightLift.periodQuotientMap m) (R.evenDiskPoint_add i j w).symm

lemma periodDeck_oddPoint (R : PaperHalfPeriodRealization k) (i j : ℤ)
    (w : PuncturedClosedDisk k) :
    HeightLift.periodDeck m i (R.oddPeriodPoint m j w) = R.oddPeriodPoint m (i+j) w := by
  exact congrArg (HeightLift.periodQuotientMap m) (R.oddDiskPoint_add i j w).symm

lemma evenCopyIndex_add_two (j : ZMod m) : evenCopyIndex j + 2 = evenCopyIndex (j+1) := by
  calc
    evenCopyIndex j + 2 = (evenCopyIndex j + 1) + 1 := by ring
    _ = evenCopyIndex (j+1) := by rw [evenCopyIndex_succ, oddCopyIndex_succ]

lemma oddCopyIndex_add_two (j : ZMod m) : oddCopyIndex j + 2 = oddCopyIndex (j+1) := by
  calc
    oddCopyIndex j + 2 = (oddCopyIndex j + 1) + 1 := by ring
    _ = oddCopyIndex (j+1) := by rw [oddCopyIndex_succ, evenCopyIndex_succ]

lemma periodDeck_orderedDiskPoint (R : PaperHalfPeriodRealization k)
    (n : ZMod (2*m)) (w : PuncturedClosedDisk k) :
    HeightLift.periodDeck m 1 (R.orderedDiskPoint n w) = R.orderedDiskPoint (n+2) w := by
  obtain ⟨j, rfl | rfl⟩ := copyIndex_cases n
  · rw [evenCopyIndex_add_two]
    have hj : ((j.val : ℤ) : ZMod m) = j := by simp
    have hs : ((1 + (j.val : ℤ)) : ZMod m) = j+1 := by simp [add_comm]
    rw [← hj, orderedDiskPoint_even_int, periodDeck_evenPoint]
    rw [hj, ← hs]
    simpa only [Int.cast_add, Int.cast_one] using
      (R.orderedDiskPoint_even_int (1 + (j.val : ℤ)) w).symm
  · rw [oddCopyIndex_add_two]
    have hj : ((j.val : ℤ) : ZMod m) = j := by simp
    have hs : ((1 + (j.val : ℤ)) : ZMod m) = j+1 := by simp [add_comm]
    rw [← hj, orderedDiskPoint_odd_int, periodDeck_oddPoint]
    rw [hj, ← hs]
    simpa only [Int.cast_add, Int.cast_one] using
      (R.orderedDiskPoint_odd_int (1 + (j.val : ℤ)) w).symm

lemma encode_translation_pullback (R : PaperHalfPeriodRealization k)
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) :
    encodeDiskFunction (R.diskFunctionPullback (f ∘ HeightLift.periodDeck m 1)) =
      SurfaceSym.shiftF (encodeDiskFunction (R.diskFunctionPullback f)) := by
  funext n z
  by_cases hz : z ∉ Surface.punctures k ∧ ‖z‖ ≤ 1
  · let w : PuncturedClosedDisk k := ⟨⟨z,hz.1⟩,hz.2⟩
    change encodeDiskFunction _ n w.val.val = encodeDiskFunction _ (n+2) w.val.val
    rw [encodeDiskFunction_on_disk, encodeDiskFunction_on_disk]
    change f (HeightLift.periodDeck m 1 (R.orderedDiskPoint n w)) = f (R.orderedDiskPoint (n+2) w)
    rw [R.periodDeck_orderedDiskPoint]
  · simp only [encodeDiskFunction, SurfaceSym.shiftF, dite_eq_right hz]

/-- The translation eigenvalue is unchanged by the actual-to-model encoding:
there is no conjugation or inverse phase in this pullback convention. -/
lemma translation_eigenvalue_iff (R : PaperHalfPeriodRealization k)
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (c : ℂ) :
    (∀ q, f (HeightLift.periodDeck m 1 q) = c * f q) ↔
      ∀ n z, SurfaceSym.shiftF (encodeDiskFunction (R.diskFunctionPullback f)) n z =
        c * encodeDiskFunction (R.diskFunctionPullback f) n z := by
  constructor
  · intro hf n z
    by_cases hz : z ∉ Surface.punctures k ∧ ‖z‖ ≤ 1
    · let w : PuncturedClosedDisk k := ⟨⟨z,hz.1⟩,hz.2⟩
      change encodeDiskFunction _ (n+2) w.val.val = c * encodeDiskFunction _ n w.val.val
      rw [encodeDiskFunction_on_disk, encodeDiskFunction_on_disk]
      change f (R.orderedDiskPoint (n+2) w) = c * f (R.orderedDiskPoint n w)
      rw [← R.periodDeck_orderedDiskPoint]
      exact hf _
    · simp only [SurfaceSym.shiftF, encodeDiskFunction, dite_eq_right hz, mul_zero]
  · intro hf q
    obtain ⟨p, rfl⟩ := R.orderedDiskPoint_surjective q
    have he := hf p.1 p.2.val.val
    change encodeDiskFunction _ (p.1+2) p.2.val.val = c * encodeDiskFunction _ p.1 p.2.val.val at he
    rw [encodeDiskFunction_on_disk, encodeDiskFunction_on_disk] at he
    rw [R.periodDeck_orderedDiskPoint]
    exact he

lemma compactSmooth_translation_pullback (R : PaperHalfPeriodRealization k)
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) :
    letI := HeightLift.periodChartedSpace R.hC m
    (ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f ∧ HasCompactSupport f) →
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (f ∘ HeightLift.periodDeck m 1) ∧
        HasCompactSupport (f ∘ HeightLift.periodDeck m 1) := by
  intro hf
  apply (R.compactSmooth_iff_encoding_mem_CcSmooth _).mpr
  rw [R.encode_translation_pullback]
  exact SurfaceSym.shiftF_mem_CcSmooth ((R.compactSmooth_iff_encoding_mem_CcSmooth f).mp hf)

end PaperHalfPeriodRealization
end KsIndex.KarcherData
