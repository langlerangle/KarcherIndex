module

public import KsIndexLean.KarcherHeightCayley
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

@[expose] public section


/-! A simple-zero holomorphic coordinate at each EW end puncture. -/
noncomputable section
open Filter
open scoped Topology
namespace KsIndex.KarcherData

/-- Choose the Cayley coordinate or its reciprocal so the chosen end is a zero. -/
def endCoordinate (k : ℕ) (w z : ℂ) : ℂ :=
  (1 + (endSign k w : ℂ) * Complex.I * z ^ k) /
    (1 - (endSign k w : ℂ) * Complex.I * z ^ k)

lemma endSign_mul_power {k : ℕ} {w : ℂ} (hw : w ∈ Surface.punctures k) :
    (endSign k w : ℂ) * w ^ k = Complex.I := by
  rcases puncture_power_sign hw with hp | hp
  · simp [endSign, hp]
  · have hn : -Complex.I ≠ Complex.I := by
      intro he
      have hi := congrArg Complex.im he
      norm_num at hi
    simp [endSign, hp, hn]

lemma endCoordinate_factors {k : ℕ} {w : ℂ} (hw : w ∈ Surface.punctures k) :
    1 + (endSign k w : ℂ) * Complex.I * w ^ k = 0 ∧
    1 - (endSign k w : ℂ) * Complex.I * w ^ k = 2 := by
  have he : (endSign k w : ℂ) * Complex.I * w ^ k = -1 := by
    calc
      _ = Complex.I * ((endSign k w : ℂ) * w ^ k) := by ring
      _ = -1 := by rw [endSign_mul_power hw, Complex.I_mul_I]
  constructor <;> rw [he] <;> ring

@[simp] lemma endCoordinate_self {k : ℕ} {w : ℂ} (hw : w ∈ Surface.punctures k) :
    endCoordinate k w w = 0 := by
  unfold endCoordinate
  rw [(endCoordinate_factors hw).1, zero_div]

lemma hasStrictDerivAt_endCoordinate {k : ℕ} {w : ℂ} (hw : w ∈ Surface.punctures k) :
    HasStrictDerivAt (endCoordinate k w)
      ((endSign k w : ℂ) * Complex.I * (k : ℂ) * w ^ (k - 1) / 2) w := by
  let a : ℂ := (endSign k w : ℂ) * Complex.I
  have hp := (hasStrictDerivAt_pow k w).const_mul a
  have hd : 1 - a * w ^ k ≠ 0 := by
    rw [show 1 - a * w ^ k = 2 from (endCoordinate_factors hw).2]
    norm_num
  have ht := (hp.const_add 1).div (hp.const_sub 1) hd
  have he : (a * ((k : ℂ) * w ^ (k - 1)) * (1 - a * w ^ k) -
      (1 + a * w ^ k) * -(a * ((k : ℂ) * w ^ (k - 1)))) / (1 - a * w ^ k) ^ 2 =
      (endSign k w : ℂ) * Complex.I * (k : ℂ) * w ^ (k - 1) / 2 := by
    dsimp [a]
    rw [(endCoordinate_factors hw).1, (endCoordinate_factors hw).2]
    ring
  exact ht.congr_deriv he

lemma endCoordinate_deriv_ne_zero {k : ℕ} (hk : 2 ≤ k) {w : ℂ}
    (hw : w ∈ Surface.punctures k) :
    (endSign k w : ℂ) * Complex.I * (k : ℂ) * w ^ (k - 1) / 2 ≠ 0 := by
  have hs : (endSign k w : ℂ) ≠ 0 := by unfold endSign; split_ifs <;> norm_num
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hs Complex.I_ne_zero)
    (by exact_mod_cast (show k ≠ 0 by omega)))
    (pow_ne_zero _ (puncture_ne_zero hk hw))) (by norm_num)

/-- The end coordinate is locally invertible, with its image centered at zero. -/
theorem endCoordinate_map_nhds {k : ℕ} (hk : 2 ≤ k) {w : ℂ}
    (hw : w ∈ Surface.punctures k) :
    Filter.map (endCoordinate k w) (𝓝 w) = 𝓝 (0 : ℂ) := by
  simpa only [endCoordinate_self hw] using
    (hasStrictDerivAt_endCoordinate hw).map_nhds_eq (endCoordinate_deriv_ne_zero hk hw)

/-- The coordinate is literally the height Cayley function or its reciprocal. -/
lemma endCoordinate_eq_heightCayley (k : ℕ) (w z : ℂ) :
    endCoordinate k w z =
      if w ^ k = Complex.I then heightCayley k z else (heightCayley k z)⁻¹ := by
  by_cases hp : w ^ k = Complex.I
  · simp [endCoordinate, endSign, hp, heightCayley]
  · simp [endCoordinate, endSign, hp, heightCayley, inv_div, sub_eq_add_neg]

/-- A genuine local inverse at the puncture, with both inverse identities and
nonzero inverse derivative, in the base complex plane. `KarcherEndCoordinateChart`
packages the inverse-function chart and its restriction to the punctured plane. -/
theorem exists_endCoordinate_local_inverse {k : ℕ} (hk : 2 ≤ k) {w : ℂ}
    (hw : w ∈ Surface.punctures k) :
    ∃ g : ℂ → ℂ,
      HasStrictDerivAt g
        (((endSign k w : ℂ) * Complex.I * (k : ℂ) * w ^ (k - 1) / 2)⁻¹) 0 ∧
      (∀ᶠ z in 𝓝 w, g (endCoordinate k w z) = z) ∧
      (∀ᶠ z in 𝓝 (0 : ℂ), endCoordinate k w (g z) = z) := by
  have hf := hasStrictDerivAt_endCoordinate hw
  have hn := endCoordinate_deriv_ne_zero hk hw
  let g := hf.localInverse _ _ _ hn
  refine ⟨g, ?_, ?_, ?_⟩
  · simpa only [endCoordinate_self hw] using hf.to_localInverse hn
  · exact hf.eventually_left_inverse hn
  · simpa only [endCoordinate_self hw] using hf.eventually_right_inverse hn

end KsIndex.KarcherData
