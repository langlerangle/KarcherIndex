module

public import KsIndexLean.KarcherPeriodicLift

@[expose] public section


/-! Functions on a period quotient and deck-periodic functions on its height lift. -/
noncomputable section
namespace KsIndex.KarcherData.HeightLift
variable {P : Type*} {F : P → PeriodTarget}

/-- Complex functions invariant under translation by multiples of `m` full periods. -/
def periodicFunctions (m : ℕ) : Submodule ℂ (HeightLift F → ℂ) where
  carrier := {f | ∀ n : ℤ, ∀ q, f (deck (n*(m : ℤ)) q) = f q}
  zero_mem' := by
    change ∀ n : ℤ, ∀ q : HeightLift F, (0 : ℂ) = 0
    intros
    rfl
  add_mem' := by
    intro f g hf hg n q
    exact congrArg₂ (· + ·) (hf n q) (hg n q)
  smul_mem' := by
    intro c f hf n q
    exact congrArg (c • ·) (hf n q)

/-- Pullback and descent identify all quotient functions with periodic lift functions. -/
def periodicFunctionEquiv (m : ℕ) :
    (PeriodQuotient F m → ℂ) ≃ₗ[ℂ] periodicFunctions (F := F) m where
  toFun g := ⟨fun q => g (Quotient.mk _ q), by
    intro n q
    have he : (Quotient.mk _ q : PeriodQuotient F m) =
        Quotient.mk _ (deck (n*(m : ℤ)) q) := Quotient.sound ⟨n, rfl⟩
    exact congrArg g he.symm⟩
  invFun f := Quotient.lift f.val (by
    rintro q r ⟨n, rfl⟩
    exact (f.property n q).symm)
  left_inv g := by
    funext q
    refine Quotient.inductionOn q ?_
    intro q
    rfl
  right_inv f := by
    apply Subtype.ext
    rfl
  map_add' f g := by
    apply Subtype.ext
    rfl
  map_smul' c f := by
    apply Subtype.ext
    rfl

/-- The quotient and its periodic pullback have the same pointwise norm bounds. -/
lemma periodicFunctionEquiv_norm_bound_iff (m : ℕ) (g : PeriodQuotient F m → ℂ) (C : ℝ) :
    (∀ q, ‖(periodicFunctionEquiv m g).val q‖ ≤ C) ↔ ∀ x, ‖g x‖ ≤ C := by
  constructor
  · intro h x
    refine Quotient.inductionOn x ?_
    intro q
    exact h q
  · intro h q
    exact h (Quotient.mk _ q)

end KsIndex.KarcherData.HeightLift

#print axioms KsIndex.KarcherData.HeightLift.periodicFunctionEquiv
#print axioms KsIndex.KarcherData.HeightLift.periodicFunctionEquiv_norm_bound_iff
