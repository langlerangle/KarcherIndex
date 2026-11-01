module

public import KsIndexLean.KarcherDiskFunctions
public import KsIndexLean.JacobiFamily

@[expose] public section


/-! Canonical total-function encoding of genuine disk families. Values at deleted
punctures and outside the closed disk are set to zero. -/
noncomputable section
open scoped Classical
namespace KsIndex.KarcherData
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

/-- Zero extension changes only coordinates that are absent from the actual surface. -/
def encodeDiskFunction (u : CompatibleDiskFunctions k m) (n : ZMod (2 * m)) (w : ℂ) : ℂ :=
  if hw : w ∉ Surface.punctures k ∧ ‖w‖ ≤ 1 then
    u.val (n, ⟨⟨w, hw.1⟩, hw.2⟩) else 0

lemma encodeDiskFunction_on_disk (u : CompatibleDiskFunctions k m)
    (n : ZMod (2 * m)) (w : PuncturedClosedDisk k) :
    encodeDiskFunction u n w.val.val = u.val (n, w) := by
  simp only [encodeDiskFunction, dif_pos (show w.val.val ∉ Surface.punctures k ∧ ‖w.val.val‖ ≤ 1 from ⟨w.val.property, w.property⟩)]
  rfl

lemma encodeDiskFunction_punctureZero (u : CompatibleDiskFunctions k m) :
    Surface.PunctureZero k (encodeDiskFunction u) := by
  intro n p hp
  simp [encodeDiskFunction, hp]

lemma encodeDiskFunction_exterior (u : CompatibleDiskFunctions k m)
    (n : ZMod (2 * m)) (w : ℂ) (hw : 1 < ‖w‖) : encodeDiskFunction u n w = 0 := by
  simp [encodeDiskFunction, not_le.mpr hw]

lemma encodeDiskFunction_seamVal (u : CompatibleDiskFunctions k m) :
    Surface.SeamVal k (encodeDiskFunction u) := by
  intro n w hw
  have hp := JacobiFamily.arc_notMem_punctures hw
  have hn : ‖w‖ ≤ 1 := le_of_eq hw.1
  let v : PuncturedClosedDisk k := ⟨⟨w, hp⟩, hn⟩
  change encodeDiskFunction u (n + 1) v.val.val = encodeDiskFunction u n v.val.val
  rw [encodeDiskFunction_on_disk, encodeDiskFunction_on_disk]
  exact u.property n v hw

lemma restrict_encodeDiskFunction (u : CompatibleDiskFunctions k m) :
    restrictSeamFamily (encodeDiskFunction u) (encodeDiskFunction_seamVal u) = u := by
  apply Subtype.ext
  funext p
  exact encodeDiskFunction_on_disk u p.1 p.2

lemma encode_restrictSeamFamily (u : ZMod (2 * m) → ℂ → ℂ)
    (hs : Surface.SeamVal k u) (hp : Surface.PunctureZero k u)
    (he : ∀ n w, 1 < ‖w‖ → u n w = 0) :
    encodeDiskFunction (restrictSeamFamily u hs) = u := by
  funext n w
  unfold encodeDiskFunction
  split_ifs with hw
  · rfl
  · by_cases hwp : w ∈ Surface.punctures k
    · exact (hp n w hwp).symm
    · exact (he n w (lt_of_not_ge (fun hn => hw ⟨hwp, hn⟩))).symm

namespace PaperHalfPeriodRealization

/-- The actual quotient function represented by a normalized model Jacobi field.
Its geometric differential equation is a separate transport obligation. -/
def boundedJacobiFunction (R : PaperHalfPeriodRealization k)
    (u : Surface.BoundedJacobi k m) :
    HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ :=
  R.diskFunctionDescend (restrictSeamFamily u.val u.property.2.2.2.2)

lemma boundedJacobiFunction_bounded (R : PaperHalfPeriodRealization k)
    (u : Surface.BoundedJacobi k m) : ∃ C : ℝ, ∀ q, ‖R.boundedJacobiFunction u q‖ ≤ C := by
  obtain ⟨C, hC⟩ := u.property.2.1
  refine ⟨C, ?_⟩
  apply (R.diskFunctionDescend_norm_bound_iff _ C).mpr
  intro p
  exact hC p.1 p.2.val.val

lemma boundedJacobiFunction_injective (R : PaperHalfPeriodRealization k) :
    Function.Injective (R.boundedJacobiFunction (m := m)) := by
  intro u v huv
  have hrest : restrictSeamFamily u.val u.property.2.2.2.2 =
      restrictSeamFamily v.val v.property.2.2.2.2 := by
    apply Subtype.ext
    funext p
    have he := congrFun huv (R.orderedDiskPoint p.1 p.2)
    simpa only [boundedJacobiFunction, diskFunctionDescend_apply] using he
  have he := congrArg encodeDiskFunction hrest
  rw [encode_restrictSeamFamily u.val _ u.property.2.2.2.1 u.property.1.2.2,
    encode_restrictSeamFamily v.val _ v.property.2.2.2.1 v.property.1.2.2] at he
  exact Subtype.ext he

end PaperHalfPeriodRealization
end KsIndex.KarcherData
