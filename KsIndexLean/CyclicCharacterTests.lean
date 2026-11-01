module

public import KsIndexLean.CubicCharacterTests

@[expose] public section


noncomputable section
namespace KsIndex.Trace
section Algebra
variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Finite cyclic averaging needs no topology or choice of basis. -/
lemma cyclic_invariant_tests_suffice (S : E →ₗ[ℂ] E) (n : ℕ) (hn : 0 < n)
    (hS : ∀ v, (S ^ n) v = v) (D : Submodule ℂ E)
    (hD : ∀ v ∈ D, S v ∈ D) (L : E →ₗ[ℂ] ℂ)
    (hL : ∀ v, L (S v) = L v)
    (hzero : ∀ v ∈ D, S v = v → L v = 0) :
    ∀ v ∈ D, L v = 0 := by
  intro v hv
  have hmem (i : ℕ) : (S ^ i) v ∈ D := by
    induction i with
    | zero => simpa using hv
    | succ i hi => simpa only [pow_succ', Module.End.mul_apply] using hD _ hi
  have hpair (i : ℕ) : L ((S ^ i) v) = L v := by
    induction i with
    | zero => rfl
    | succ i hi => simpa only [pow_succ', Module.End.mul_apply, hL] using hi
  let w := ∑ i ∈ Finset.range n, (S ^ i) v
  have hw : w ∈ D := D.sum_mem (fun i _ => hmem i)
  have hfix : S w = w := by
    dsimp [w]
    simp only [map_sum, ← Module.End.mul_apply, ← pow_succ']
    have hs := Finset.sum_range_succ' (fun i => (S ^ i) v) n
    rw [Finset.sum_range_succ] at hs
    simp only [hS, pow_zero, Module.End.one_apply] at hs
    exact add_right_cancel hs.symm
  have hz := hzero w hw hfix
  have hp : L w = (n : ℂ) * L v := by
    simp [w, map_sum, hpair]
  rw [hp] at hz
  exact (mul_eq_zero.mp hz).resolve_left (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))

/-- Arbitrary finite-order character tests suffice on an invariant domain. -/
lemma cyclicCharacter_tests_suffice (T : E →ₗ[ℂ] E) (c : ℂ)
    (n : ℕ) (hn : 0 < n) (hc : c ^ n = 1)
    (hT : ∀ v, (T ^ n) v = v) (D : Submodule ℂ E)
    (hD : ∀ v ∈ D, T v ∈ D) (L : E →ₗ[ℂ] ℂ)
    (hL : ∀ v, L (T v) = c * L v)
    (hzero : ∀ v ∈ D, T v = c • v → L v = 0) :
    ∀ v ∈ D, L v = 0 := by
  have hc0 : c ≠ 0 := by
    intro he
    rw [he, zero_pow (Nat.ne_of_gt hn)] at hc
    exact zero_ne_one hc
  let S : E →ₗ[ℂ] E := c⁻¹ • T
  have hp (i : ℕ) (v : E) : (S ^ i) v = (c⁻¹) ^ i • (T ^ i) v := by
    induction i with
    | zero => simp
    | succ i hi =>
      simp only [pow_succ', Module.End.mul_apply, hi, S, LinearMap.smul_apply,
        map_smul, smul_smul, mul_comm]
  apply cyclic_invariant_tests_suffice S n hn ?_ D ?_ L ?_ ?_
  · intro v
    rw [hp, hT, inv_pow, hc, inv_one, one_smul]
  · intro v hv
    exact D.smul_mem _ (hD v hv)
  · intro v
    change L (c⁻¹ • T v) = L v
    rw [map_smul, smul_eq_mul, hL, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  · intro v hv he
    apply hzero v hv
    have h := congrArg (fun w => c • w) he
    simpa only [S, LinearMap.smul_apply, smul_smul, mul_inv_cancel₀ hc0, one_smul] using h

end Algebra
end KsIndex.Trace
