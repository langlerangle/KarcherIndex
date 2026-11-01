module

public import KsIndexLean.KarcherPeriodOperations
public import KsIndexLean.KarcherLoopCircleCheck
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section


/-! Exact periods for certified finite piecewise-C¹ closed chains, over all basepoints.
This does not assert connectivity, prescribed-basepoint transport, or a surface cover. -/
noncomputable section
namespace KsIndex.KarcherData
open Piecewise

lemma exists_positive_end {k : ℕ} (hk : 2 ≤ k) :
    ∃ z : ℂ, z ∈ Surface.punctures k ∧ z ^ k = Complex.I := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq Complex.I (show 0 < k by omega)
  refine ⟨z, ?_, hz⟩
  change z ^ (2 * k) = -1
  rw [Nat.mul_comm 2 k, pow_mul, hz, Complex.I_sq]

/-- A counterclockwise circle at a proved positive end gives the actual +2π period.
The contour equalities come from `exists_small_circle_loop_formula_check`. -/
theorem exists_period_generator {k : ℕ} (hk : 2 ≤ k) :
    ∃ C : Chain, C.IsClosed ∧ (∀ z ∈ Surface.punctures k, C.Avoids z) ∧
      periodVector k C = (0, 0, 2 * Real.pi) := by
  obtain ⟨z, hz, hpow⟩ := exists_positive_end hk
  obtain ⟨ε, hε, hdata⟩ := exists_small_circle_loop_formula_check hk hz
  obtain ⟨hA, _, _, _, h1, h2, h3⟩ := hdata (ε / 2) (by linarith) (by linarith)
  refine ⟨circleChain z (ε / 2), circleChain_closed _ _, hA, ?_⟩
  unfold periodVector
  rw [h1.2.1, h2.2.1, h3.2.1, residue1_real_factor, residue2_real_factor,
    residue3_real_endSign hz]
  simp [endSign, hpow]

/-- Construct each integer period by actual repetition and reversal at the generator's
own nonpuncture basepoint. The existential statement does not prescribe that basepoint. -/
theorem exists_integer_period {k : ℕ} (hk : 2 ≤ k) (n : ℤ) :
    ∃ C : Chain, C.IsClosed ∧ (∀ z ∈ Surface.punctures k, C.Avoids z) ∧
      periodVector k C = (0, 0, (2 * Real.pi) * (n : ℝ)) := by
  obtain ⟨C, hc, hA, hp⟩ := exists_period_generator hk
  cases n with
  | ofNat m =>
    refine ⟨C.natRepeat hc m, C.repeat_closed hc m,
      fun z hz => C.repeat_avoids hc (hA z hz) m, ?_⟩
    rw [periodVector_natRepeat hk C hc hA m, hp]
    simp [Prod.smul_mk, smul_eq_mul, mul_comm]
  | negSucc m =>
    have hrev : ∀ z ∈ Surface.punctures k, C.reverse.Avoids z :=
      fun z hz => C.reverse_avoids (hA z hz)
    refine ⟨C.reverse.natRepeat (C.reverse_closed hc) (m + 1),
      C.reverse.repeat_closed (C.reverse_closed hc) (m + 1),
      fun z hz => C.reverse.repeat_avoids (C.reverse_closed hc) (hrev z hz) (m + 1), ?_⟩
    rw [periodVector_natRepeat hk C.reverse (C.reverse_closed hc) hrev,
      periodVector_reverse hk C hA, hp]
    simp [Prod.smul_mk, smul_eq_mul, mul_comm]
    ring

/-- The exact set of actual real periods for the stated certified loop class.
Basepoints range freely; no assertion about a prescribed basepoint is made. -/
theorem periodSet_eq {k : ℕ} (hk : 2 ≤ k) :
    periodSet k = {p | ∃ n : ℤ, p = (0, 0, (2 * Real.pi) * (n : ℝ))} := by
  apply Set.Subset.antisymm (periodSet_subset hk)
  rintro p ⟨n, rfl⟩
  obtain ⟨C, hc, hA, hp⟩ := exists_integer_period hk n
  exact ⟨C, hc, hA, hp.symm⟩

end KsIndex.KarcherData
