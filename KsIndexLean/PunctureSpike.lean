module

/-
# Point-supported functions at deleted punctures

`Surface.PunctureZero` normalizes representatives to zero at deleted punctures.
These values are outside the surface domain, so the normalization is a choice of
representative, not a boundary condition. The point-supported function `spike`
illustrates why such a normalization is needed: its restriction to the punctured
chain vanishes, although the representative itself does not.

For `k ≥ 1`, `pt k = exp(iπ/(2k))` is a deleted puncture, and `spike_not_mem`
proves that the spike there cannot belong to `BoundedJacobi`. The complementary
uniqueness statement, `Surface.boundedJacobi_ext`, says that two members agreeing
on the actual chain domain are equal as representatives.

The point-supported counterexample was identified by GPT-5.6 Sol.
-/
public import KsIndexLean.Surface
public import KsIndexLean.SurfaceTargets

@[expose] public section


noncomputable section

open Complex Real Set Filter
open KsIndex.Surface

namespace KsIndex.PunctureSpike

variable {k m : ℕ}

/-- The spike: `1` at `(n₀, p)`, `0` everywhere else. -/
def spike (m : ℕ) (n₀ : ZMod (2 * m)) (p : ℂ) : ZMod (2 * m) → ℂ → ℂ :=
  fun n w => if n = n₀ ∧ w = p then 1 else 0

lemma spike_self {m : ℕ} (n₀ : ZMod (2 * m)) (p : ℂ) : spike m n₀ p n₀ p = 1 := by
  unfold spike
  rw [if_pos ⟨rfl, rfl⟩]

/-- The explicit junction point `pt k = e^{iπ/(2k)}`. -/
def pt (k : ℕ) : ℂ := Complex.exp (((π / (2 * k) : ℝ) : ℂ) * Complex.I)

/-- `pt k` is a deleted puncture: `(pt k)^{2k} = e^{iπ} = −1`. -/
lemma pt_mem_punctures (hk : 1 ≤ k) : pt k ∈ punctures k := by
  show (pt k) ^ (2 * k) = -1
  unfold pt
  rw [← Complex.exp_nat_mul]
  have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [show ((2 * k : ℕ) : ℂ) * (((π / (2 * k) : ℝ) : ℂ) * Complex.I)
      = ((π : ℝ) : ℂ) * Complex.I from by push_cast; field_simp]
  simpa using Complex.exp_pi_mul_I

/-- The puncture spike is not in `BoundedJacobi`: it violates
the `PunctureZero` normalization at `pt k`. -/
theorem spike_not_mem (hk : 1 ≤ k) (n₀ : ZMod (2 * m)) :
    spike m n₀ (pt k) ∉ BoundedJacobi k m := by
  intro hmem
  have h := hmem.2.2.2.1 n₀ (pt k) (pt_mem_punctures hk)
  rw [spike_self] at h
  exact one_ne_zero h

end KsIndex.PunctureSpike
