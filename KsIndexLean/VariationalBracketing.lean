module

public import KsIndexLean.DiskJacobiMinMax
public import KsIndexLean.FiniteCopyJacobiMinMax

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]

/-- An injective form/mass preserving inclusion transports a trial space with
its dimension and energy bound intact. The two ambient L2 closures may differ. -/
lemma trial_bound_transport (T : E →ₗ[ℂ] F) (hT : Function.Injective T)
    (Q M : E → ℝ) (R N : F → ℝ)
    (hQ : ∀ u, R (T u) = Q u) (hM : ∀ u, N (T u) = M u)
    (d : ℕ) (L : ℝ)
    (h : ∃ W : Submodule ℂ E, FiniteDimensional ℂ W ∧ Module.finrank ℂ W = d ∧
      ∀ u : W, Q u ≤ L * M u) :
    ∃ W : Submodule ℂ F, FiniteDimensional ℂ W ∧ Module.finrank ℂ W = d ∧
      ∀ u : W, R u ≤ L * N u := by
  obtain ⟨W, hfd, hd, hbound⟩ := h
  let := hfd
  let e := Submodule.equivMapOfInjective T hT W
  let : FiniteDimensional ℂ (W.map T) := e.finiteDimensional
  refine ⟨W.map T, inferInstance, e.finrank_eq.symm.trans hd, ?_⟩
  intro u
  obtain ⟨v, hv, he⟩ := u.property
  have h := hbound ⟨v, hv⟩
  change R u.val ≤ L * N u.val
  rw [← he, hQ, hM]
  exact h

/-- Same-index eigenvalue bracketing from attained min-max characterizations.
The smaller form domain gives the larger eigenvalue. This statement applies
to finite or infinite enumerations at every index available on both sides. -/
lemma eigenvalue_le_of_trial_inclusion (T : E →ₗ[ℂ] F) (hT : Function.Injective T)
    (Q M : E → ℝ) (R N : F → ℝ)
    (hQ : ∀ u, R (T u) = Q u) (hM : ∀ u, N (T u) = M u)
    (d : ℕ) (a b : ℝ)
    (ha : ∀ L, a ≤ L ↔ ∃ W : Submodule ℂ E,
      FiniteDimensional ℂ W ∧ Module.finrank ℂ W = d ∧ ∀ u : W, Q u ≤ L * M u)
    (hb : ∀ L, b ≤ L ↔ ∃ W : Submodule ℂ F,
      FiniteDimensional ℂ W ∧ Module.finrank ℂ W = d ∧ ∀ u : W, R u ≤ L * N u) :
    b ≤ a :=
  (hb a).mpr (trial_bound_transport T hT Q M R N hQ hM d a ((ha a).mp le_rfl))

end KsIndex.Spectral
