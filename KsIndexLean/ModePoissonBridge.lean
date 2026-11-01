module

/-
The per-mode Poisson identity.

`ArcPoisson.poissonExt_monomial` reproduces a boundary exponential as the harmonic
monomial in polar form, `P[e^{iℓ·}] w = ‖w‖^{|ℓ|}·e^{iℓ·arg w}`.  This file bridges that to
the `baseMode` of `ModePoisson`: writing `w = ‖w‖·e^{i·arg w}` (`norm_mul_exp_arg_mul_I`),

  `baseMode k r n w = ‖w‖^{|ℓ(n)|}·e^{iℓ(n)·arg w}`        (`baseMode_polar`, unconditional),

so for `‖w‖ < 1`

  `baseMode k r n w = poissonExt (fun φ => e^{iℓ(n)φ}) w`   (`baseMode_eq_poissonExt`).

Both branches of `baseMode` (holomorphic when `ℓ(n) ≥ 0`, conjugate when `ℓ(n) < 0`) are covered
by the SIGNED exponent `ℓ(n) = lz k r n`: the polar phase `e^{iℓ·arg w}` carries the sign, and the
conjugate branch is `e^{−i|ℓ|·arg w}` exactly.  This is the term in the Poisson kernel expansion — `Σ_m ‖w‖^{|m|}e^{im·arg w}·f̂(m)` reindexed along the progression `m = ℓ(n)`.
-/
public import KsIndexLean.ModePoisson
public import KsIndexLean.ArcPoisson

@[expose] public section


noncomputable section

open Real Set Complex
open KsIndex.Surface KsIndex.SingleDisk KsIndex.ModeKit KsIndex.ModeWitness
  KsIndex.ModePoisson KsIndex.ArcPoisson

namespace KsIndex.ModePoissonBridge

variable {k r : ℕ}

/-- Polar form of a natural power: `w^p = ‖w‖^p·e^{i p·arg w}`. -/
lemma pow_polar (w : ℂ) (p : ℕ) :
    w ^ p = ((‖w‖ ^ p : ℝ) : ℂ) * Complex.exp ((p : ℂ) * ↑(Complex.arg w) * Complex.I) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I w]
  rw [mul_pow, ← Complex.ofReal_pow, ← Complex.exp_nat_mul, mul_assoc]

/-- **The polar form of `baseMode`** (unconditional): `baseMode k r n w = ‖w‖^{|ℓ(n)|}·e^{iℓ(n)·arg w}`,
with `ℓ(n) = lz k r n` the SIGNED angular index. -/
lemma baseMode_polar (k r : ℕ) (n : ℤ) (w : ℂ) :
    baseMode k r n w
      = ((‖w‖ ^ (lz k r n).natAbs : ℝ) : ℂ)
        * Complex.exp (↑(lz k r n) * ↑(Complex.arg w) * Complex.I) := by
  unfold baseMode
  split
  · rename_i hpos
    show w ^ (lz k r n).natAbs = _
    set p := (lz k r n).natAbs with hp
    have hlz : ((lz k r n : ℤ) : ℂ) = (p : ℂ) := by
      have h : (lz k r n : ℤ) = (p : ℤ) := by rw [hp]; omega
      exact_mod_cast h
    rw [pow_polar]
    congr 2
    rw [hlz]
  · rename_i hneg
    show conjF (fun w => w ^ (lz k r n).natAbs) w = _
    simp only [conjF]
    set p := (lz k r n).natAbs with hp
    have hlz : ((lz k r n : ℤ) : ℂ) = -(p : ℂ) := by
      have h : (lz k r n : ℤ) = -(p : ℤ) := by rw [hp]; omega
      exact_mod_cast h
    rw [pow_polar, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_natCast]
    rw [hlz]; ring

/-- **The per-mode Poisson bridge**: on the open disk, `baseMode k r n` is the Poisson extension of
the boundary exponential `e^{iℓ(n)φ}`. -/
lemma baseMode_eq_poissonExt (k r : ℕ) (n : ℤ) {w : ℂ} (hw1 : ‖w‖ < 1) :
    baseMode k r n w
      = poissonExt (fun φ => Complex.exp (↑(lz k r n) * ↑φ * Complex.I)) w := by
  rw [poissonExt_monomial hw1 (lz k r n), baseMode_polar]

end KsIndex.ModePoissonBridge
