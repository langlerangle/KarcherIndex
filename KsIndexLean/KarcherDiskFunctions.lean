module

public import KsIndexLean.KarcherDiskGluingTopology

@[expose] public section


/-! Single-valued disk families and functions on the actual EW period quotient. -/
noncomputable section
open Set Topology
namespace KsIndex.KarcherData
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

/-- Families on the genuine punctured closed disks, with equal values on shared seams. -/
def CompatibleDiskFunctions (k m : ℕ) [Fact (2 ≤ k)] [NeZero m] :
    Submodule ℂ (ZMod (2 * m) × PuncturedClosedDisk k → ℂ) where
  carrier := {u | ∀ n w, w.val.val ∈ Surface.seamArc k m n → u (n + 1, w) = u (n, w)}
  zero_mem' := by
    change ∀ n w, w.val.val ∈ Surface.seamArc k m n → (0 : ZMod (2 * m) × PuncturedClosedDisk k → ℂ) (n + 1, w) = 0
    intros; rfl
  add_mem' := by intro u v hu hv n w hw; exact congrArg₂ (· + ·) (hu n w hw) (hv n w hw)
  smul_mem' := by intro c u hu n w hw; exact congrArg (c • ·) (hu n w hw)

lemma compatibleDiskFunctions_respects (u : CompatibleDiskFunctions k m)
    {p q : ZMod (2 * m) × PuncturedClosedDisk k} (hpq : diskGluingRel p q) : u.val p = u.val q := by
  rcases p with ⟨n,w⟩
  rcases q with ⟨o,v⟩
  obtain ⟨hw, he | he | he⟩ := hpq
  · dsimp only at hw he
    subst v; subst o; rfl
  · dsimp only at hw he
    subst v
    rw [he.1]
    exact (u.property n w he.2).symm
  · dsimp only at hw he
    subst v
    rw [he.1]
    exact u.property o w he.2

/-- Restrict a total-function encoding to actual disk points; seam equality suffices. -/
def restrictSeamFamily (u : ZMod (2 * m) → ℂ → ℂ) (hu : Surface.SeamVal k u) :
    CompatibleDiskFunctions k m :=
  ⟨fun p => u p.1 p.2.val.val, fun n w hw => hu n w.val.val hw⟩

namespace PaperHalfPeriodRealization

def diskFunctionPullback (R : PaperHalfPeriodRealization k) :
    (HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
      →ₗ[ℂ] CompatibleDiskFunctions k m where
  toFun f := ⟨fun p => f (R.orderedDiskPoint p.1 p.2), by
    intro n w hw
    exact congrArg f (R.orderedDiskPoint_glues n w hw).symm⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def diskFunctionDescend (R : PaperHalfPeriodRealization k) (u : CompatibleDiskFunctions k m) :
    HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ :=
  fun q => Quotient.lift u.val (fun _ _ hpq => compatibleDiskFunctions_respects u hpq)
    (R.gluedDiskEquiv.symm q)

lemma diskFunctionDescend_apply (R : PaperHalfPeriodRealization k)
    (u : CompatibleDiskFunctions k m) (p : ZMod (2 * m) × PuncturedClosedDisk k) :
    R.diskFunctionDescend u (R.orderedDiskPoint p.1 p.2) = u.val p := by
  change Quotient.lift u.val _ (R.gluedDiskEquiv.symm (R.gluedDiskEquiv (Quotient.mk _ p))) = u.val p
  erw [Equiv.symm_apply_apply]
  rfl

/-- All functions on the actual quotient are precisely the single-valued disk families.
No smoothness or compact-support assertion is included in this equivalence. -/
def diskFunctionEquiv (R : PaperHalfPeriodRealization k) :
    (HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
      ≃ₗ[ℂ] CompatibleDiskFunctions k m where
  toLinearMap := R.diskFunctionPullback
  invFun := R.diskFunctionDescend
  left_inv := by
    intro f
    funext q
    obtain ⟨p, rfl⟩ := R.orderedDiskPoint_surjective q
    exact R.diskFunctionDescend_apply _ p
  right_inv := by
    intro u
    apply Subtype.ext
    funext p
    exact R.diskFunctionDescend_apply u p

lemma continuous_diskFunctionDescend_iff (R : PaperHalfPeriodRealization k)
    (u : CompatibleDiskFunctions k m) : Continuous (R.diskFunctionDescend u) ↔ Continuous u.val := by
  rw [R.orderedDiskMap_isQuotientMap.continuous_iff]
  have he : R.diskFunctionDescend u ∘ (fun p => R.orderedDiskPoint p.1 p.2) = u.val := by
    funext p
    exact R.diskFunctionDescend_apply u p
  rw [he]

lemma diskFunctionDescend_norm_bound_iff (R : PaperHalfPeriodRealization k)
    (u : CompatibleDiskFunctions k m) (C : ℝ) :
    (∀ q, ‖R.diskFunctionDescend u q‖ ≤ C) ↔ ∀ p, ‖u.val p‖ ≤ C := by
  constructor
  · intro hb p
    simpa only [diskFunctionDescend_apply] using hb (R.orderedDiskPoint p.1 p.2)
  · intro hb q
    obtain ⟨p, rfl⟩ := R.orderedDiskPoint_surjective q
    simpa only [diskFunctionDescend_apply] using hb p

end PaperHalfPeriodRealization
end KsIndex.KarcherData
