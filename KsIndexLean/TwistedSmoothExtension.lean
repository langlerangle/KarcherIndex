module

public import KsIndexLean.TwistedPair

@[expose] public section


/-! Cyclic smooth extension without the compact-support hypothesis of extF_mem. -/
noncomputable section
open scoped ContDiff
namespace KsIndex.Twisted
open KsIndex.Surface KsIndex.SurfaceForm

lemma extF_isSmooth {k m : ℕ} [NeZero m] {ζ : ℂ} (hζm : ζ ^ m = 1)
    {v : ZMod (2 * 1) → ℂ → ℂ} (hv : IsSmoothTw k ζ v) :
    IsSmooth k m (extF m ζ v) := by
  have : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  have : Fact (1 < 2 * m) := ⟨by have := NeZero.ne m; omega⟩
  obtain ⟨hsm1, hsm2, hsm3, hsm4⟩ := hv
  refine ⟨fun n => contDiffOn_const.mul (hsm1 _), fun n w hw => ?_, fun n w hw => ?_⟩
  · rw [glue_extF hζm]
    refine contDiffAt_const.mul ?_
    have hval : (n + 1).val = (n.val + 1) % (2 * m) := by rw [ZMod.val_add, ZMod.val_one]
    rw [seamArc_eq] at hw
    by_cases hr : n.val % 2 = 0
    · simp only [hr, ite_true]
      refine hsm2 w ?_
      rw [seamArc_one_zero]
      have hlt := ZMod.val_lt n
      have h1 : (n + 1).val = n.val + 1 := by rw [hval]; exact Nat.mod_eq_of_lt (by omega)
      have : (n + 1).val % 2 = 1 := by rw [h1]; omega
      rwa [this] at hw
    · simp only [hr, ite_false]
      refine hsm3 w ?_
      rw [seamArc_one_one]
      have hlt := ZMod.val_lt n
      have : (n + 1).val % 2 = 0 := by
        rw [hval]
        by_cases hwrap : n.val + 1 < 2 * m
        · rw [Nat.mod_eq_of_lt hwrap]; omega
        · have : n.val + 1 = 2 * m := by omega
          rw [this, Nat.mod_self]
      rwa [this] at hw
  · simp only [extF, hsm4 _ w hw, mul_zero]

end KsIndex.Twisted
