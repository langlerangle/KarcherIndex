module

public import KsIndexLean.WeakBesselGain

@[expose] public section


/-! Arbitrary-order elliptic Sobolev gain for the planar Laplacian.
These are global distribution statements. Applications to local equations use
cutoff and product estimates to supply the Sobolev hypotheses at each order. -/
noncomputable section
open scoped SchwartzMap Laplacian LineDeriv

namespace KsIndex.Weq
open TemperedDistribution

/-- The normalized elliptic operator raises the available Sobolev order by two. -/
theorem memSobolev_add_two_iff_normalized_laplacian {s : ℝ} {f : 𝓢'(ℂ, ℂ)} :
    MemSobolev (s + 2) 2 f ↔
      MemSobolev s 2 (f - ((2 * Real.pi) ^ 2)⁻¹ • Δ f) := by
  rw [← besselPotential_two_eq, memSobolev_besselPotential_iff, add_comm]

/-- The elliptic gain works at every real Sobolev order, not only at L². -/
theorem memSobolev_add_two_of_laplacian {s : ℝ} {f : 𝓢'(ℂ, ℂ)}
    (hf : MemSobolev s 2 f) (hΔ : MemSobolev s 2 (Δ f)) :
    MemSobolev (s + 2) 2 f := by
  apply memSobolev_add_two_iff_normalized_laplacian.mpr
  simpa only [Complex.coe_smul] using
    hf.sub (hΔ.smul (((2 * Real.pi) ^ 2)⁻¹ : ℝ))

theorem memSobolev_add_two_iff {s : ℝ} {f : 𝓢'(ℂ, ℂ)} :
    MemSobolev (s + 2) 2 f ↔ MemSobolev s 2 f ∧ MemSobolev s 2 (Δ f) := by
  constructor
  · intro hf
    refine ⟨hf.mono (by linarith), ?_⟩
    simpa only [add_sub_cancel_right] using hf.laplacian
  · rintro ⟨hf, hΔ⟩
    exact memSobolev_add_two_of_laplacian hf hΔ

/-- A solution with an Hˢ Laplace source gains two orders. -/
theorem memSobolev_add_two_of_equation {s : ℝ} {f g : 𝓢'(ℂ, ℂ)}
    (hf : MemSobolev s 2 f) (hg : MemSobolev s 2 g) (heq : Δ f = g) :
    MemSobolev (s + 2) 2 f :=
  memSobolev_add_two_of_laplacian hf (heq.symm ▸ hg)

lemma distribution_laplacian_complex (f : 𝓢'(ℂ, ℂ)) :
    Δ f = ∂_{(1 : ℂ)} (∂_{(1 : ℂ)} f) + ∂_{Complex.I} (∂_{Complex.I} f) := by
  rw [TemperedDistribution.laplacian_eq_sum Complex.orthonormalBasisOneI]
  simp [Fin.sum_univ_two, Complex.coe_orthonormalBasisOneI]

/-- The value and the two coordinate derivatives characterize one additional order. -/
theorem memSobolev_add_one_iff {s : ℝ} {f : 𝓢'(ℂ, ℂ)} :
    MemSobolev (s + 1) 2 f ↔
      MemSobolev s 2 f ∧ MemSobolev s 2 (∂_{(1 : ℂ)} f) ∧ MemSobolev s 2 (∂_{Complex.I} f) := by
  constructor
  · intro hf
    refine ⟨hf.mono (by linarith), ?_, ?_⟩
    · simpa only [add_sub_cancel_right] using hf.lineDerivOp (m := 1)
    · simpa only [add_sub_cancel_right] using hf.lineDerivOp (m := Complex.I)
  · rintro ⟨hf, hx, hy⟩
    have hΔ : MemSobolev (s - 1) 2 (Δ f) := by
      rw [distribution_laplacian_complex]
      exact (hx.lineDerivOp (m := 1)).add (hy.lineDerivOp (m := Complex.I))
    have h := memSobolev_add_two_of_laplacian (hf.mono (by linarith : s - 1 ≤ s)) hΔ
    convert h using 1
    ring

/-- Each directional derivative costs one order, including nonintegral orders. -/
theorem memSobolev_iterated_lineDeriv {s : ℝ} {f : 𝓢'(ℂ, ℂ)}
    (hf : MemSobolev s 2 f) (d : ℂ) (n : ℕ) :
    MemSobolev (s - n) 2 ((fun g : 𝓢'(ℂ, ℂ) => ∂_{d} g)^[n] f) := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hs : s - ((n + 1 : ℕ) : ℝ) = (s - n) - 1 := by push_cast; ring
    rw [hs]
    exact ih.lineDerivOp (m := d)

/-- L² control of all Laplace iterates through n gives H^(2n). -/
theorem memSobolev_two_mul_of_laplacian_iterates (n : ℕ) (f : 𝓢'(ℂ, ℂ))
    (h : ∀ j ≤ n, MemSobolev 0 2 ((fun g : 𝓢'(ℂ, ℂ) => Δ g)^[j] f)) :
    MemSobolev (2 * n) 2 f := by
  induction n generalizing f with
  | zero => simpa using h 0 (by omega)
  | succ n ih =>
    have hf := ih f (fun j hj => h j (by omega))
    have hΔ := ih (Δ f) (fun j hj => by
      simpa only [Function.iterate_succ_apply] using h (j + 1) (by omega))
    convert memSobolev_add_two_of_laplacian hf hΔ using 1
    push_cast
    ring

end KsIndex.Weq
