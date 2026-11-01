module

public import KsIndexLean.JacobiFields

@[expose] public section


noncomputable section
namespace KsIndex.JacobiFields
open KsIndex.Surface

/-- Multiplication by a holomorphic monomial, including the centre and degree zero. -/
lemma laplacian_mul_pow_of_hasWD (f a b : ℂ → ℂ) (ℓ : ℕ) (w Ba Ab : ℂ)
    (hf : ∀ z, HasWD f (a z) (b z) z)
    (ha : ∃ Aa, HasWD a Aa Ba w) (hb : ∃ Bb, HasWD b Ab Bb w) :
    laplacian (fun z => f z * z ^ ℓ) w =
      w ^ ℓ * laplacian f w + 4 * (ℓ : ℂ) * w ^ (ℓ - 1) * b w := by
  obtain ⟨Aa, ha⟩ := ha
  obtain ⟨Bb, hb⟩ := hb
  let A : ℂ → ℂ := fun z => f z * ((ℓ : ℂ) * z ^ (ℓ - 1)) + z ^ ℓ * a z
  let B : ℂ → ℂ := fun z => z ^ ℓ * b z
  have hp := hasWD_pow ℓ w
  have hpd := (hasWD_const (ℓ : ℂ) w).mul (hasWD_pow (ℓ - 1) w)
  have hA := ((hf w).mul hpd).add (hp.mul ha)
  have hB := hp.mul hb
  have hAf : ∃ q, HasWD A q
      ((ℓ : ℂ) * w ^ (ℓ - 1) * b w + w ^ ℓ * Ba) w := by
    refine ⟨_, hA.congr rfl ?_⟩
    simp only [mul_zero, add_zero, zero_add]
  have hBf : ∃ q, HasWD B
      (w ^ ℓ * Ab + b w * ((ℓ : ℂ) * w ^ (ℓ - 1))) q w := ⟨_, hB⟩
  have hF : ∀ z, HasWD (fun z => f z * z ^ ℓ) (A z) (B z) z := by
    intro z
    exact ((hf z).mul (hasWD_pow ℓ z)).congr rfl (by simp [B])
  rw [laplacian_eq _ A B _ _ w hF hAf hBf,
    laplacian_eq f a b Ba Ab w hf ⟨Aa, ha⟩ ⟨Bb, hb⟩]
  ring

lemma laplacian_shift_mul_pow_of_hasWD (f a b : ℂ → ℂ) (c d : ℂ) (ℓ : ℕ)
    (w Ba Ab : ℂ) (hf : ∀ z, HasWD f (a z) (b z) z)
    (ha : ∃ Aa, HasWD a Aa Ba w) (hb : ∃ Bb, HasWD b Ab Bb w) :
    laplacian (fun z => (f z * c + d) * z ^ ℓ) w =
      c * (w ^ ℓ * laplacian f w + 4 * (ℓ : ℂ) * w ^ (ℓ - 1) * b w) := by
  obtain ⟨Aa, ha⟩ := ha
  obtain ⟨Bb, hb⟩ := hb
  have hf' (z : ℂ) : HasWD (fun z => f z * c + d) (a z * c) (b z * c) z :=
    (((hf z).mul_const c).add (hasWD_const d z)).congr (by ring) (by ring)
  have ha' : ∃ q, HasWD (fun z => a z * c) q (Ba * c) w := ⟨_, ha.mul_const c⟩
  have hb' : ∃ q, HasWD (fun z => b z * c) (Ab * c) q w := ⟨_, hb.mul_const c⟩
  rw [laplacian_mul_pow_of_hasWD _ _ _ ℓ w _ _ hf' ha' hb',
    laplacian_eq _ _ _ _ _ w hf' ha' hb',
    laplacian_eq f a b Ba Ab w hf ⟨Aa, ha⟩ ⟨Bb, hb⟩]
  ring

/-- The complete polynomial/rational family satisfies its Jacobi equation,
including at zero. -/
lemma jacobi_shifted_Ffun (n ℓ : ℕ) (hn : 1 ≤ n) (w : ℂ) :
    laplacian (fun z => (Ffun n 0 0 1 z * (-(n : ℂ)) + (ℓ : ℂ)) * z ^ ℓ) w +
      (8 * (n : ℂ)^2 * (w ^ (n-1) * (starRingEnd ℂ) w ^ (n-1)) / (Dfun n w)^2) *
        ((Ffun n 0 0 1 w * (-(n : ℂ)) + (ℓ : ℂ)) * w ^ ℓ) = 0 := by
  let W : ℂ := 8 * (n : ℂ)^2 * (w ^ (n-1) * (starRingEnd ℂ) w ^ (n-1)) / (Dfun n w)^2
  have hB : W * w = 4 * (n : ℂ) * Bfun n 0 0 1 w := by
    have hp : w ^ n = w ^ (n - 1) * w := by
      rw [← pow_succ]; congr 1; omega
    dsimp [W, Bfun]
    rw [hp]
    ring
  have hp : (ℓ : ℂ) * w ^ (ℓ - 1) * w = (ℓ : ℂ) * w ^ ℓ := by
    cases ℓ with
    | zero => simp
    | succ m => simp only [Nat.add_sub_cancel, pow_succ]; ring
  have hcross : 4 * (n : ℂ) * (ℓ : ℂ) * w ^ (ℓ - 1) * Bfun n 0 0 1 w =
      W * (ℓ : ℂ) * w ^ ℓ := by
    calc
      _ = (ℓ : ℂ) * w ^ (ℓ - 1) * (4 * (n : ℂ) * Bfun n 0 0 1 w) := by ring
      _ = (ℓ : ℂ) * w ^ (ℓ - 1) * (W * w) := by rw [hB]
      _ = W * ((ℓ : ℂ) * w ^ (ℓ - 1) * w) := by ring
      _ = _ := by rw [hp]; ring
  have hj := jacobi_Ffun n 0 0 1 w
  change laplacian (Ffun n 0 0 1) w + W * Ffun n 0 0 1 w = 0 at hj
  rw [laplacian_shift_mul_pow_of_hasWD _ _ _ _ _ ℓ w _ _
    (hasWD_Ffun n 0 0 1) (hasWD_Afun n 0 0 1 w) (hasWD_Bfun n 0 0 1 w)]
  change -(n : ℂ) * (w ^ ℓ * laplacian (Ffun n 0 0 1) w +
    4 * (ℓ : ℂ) * w ^ (ℓ - 1) * Bfun n 0 0 1 w) +
    W * ((Ffun n 0 0 1 w * -(n : ℂ) + (ℓ : ℂ)) * w ^ ℓ) = 0
  linear_combination -(n : ℂ) * w ^ ℓ * hj - hcross

end KsIndex.JacobiFields
