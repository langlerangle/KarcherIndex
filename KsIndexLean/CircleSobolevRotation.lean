module

public import KsIndexLean.CircleFourierRotation
public import KsIndexLean.CircleSobolevMultiplier

@[expose] public section


/-! Rotation on every real-order coefficient Sobolev space. -/
noncomputable section
open MeasureTheory
namespace KsIndex.CircleSobolev
open KsIndex.Trace
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

lemma rotationSymbol_norm (θ : ℝ) (n : ℤ) :
    ‖fourier n (θ : AddCircle (2 * Real.pi))‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

lemma rotationSymbol_bound (s θ : ℝ) (n : ℤ) :
    ‖fourier n (θ : AddCircle (2 * Real.pi))‖ * weight s n ≤ 1 * weight s n := by
  rw [rotationSymbol_norm]

/-- All-order rotation, with the same precomposition convention as boundaryRotation. -/
def rotationCLM (s θ : ℝ) : Space s →L[ℂ] Space s :=
  multiplierCLM (s := s) (t := s) (fun n => fourier n (θ : AddCircle (2 * Real.pi)))
    (by positivity) (rotationSymbol_bound s θ)

@[simp] theorem coeff_rotationCLM (s θ : ℝ) (u : Space s) (n : ℤ) :
    coeff s (rotationCLM s θ u) n =
      fourier n (θ : AddCircle (2 * Real.pi)) * coeff s u n :=
  coeff_multiplier _ (show (0 : ℝ) ≤ 1 by norm_num) (rotationSymbol_bound s θ) u n

theorem rotationCLM_add (s θ φ : ℝ) (u : Space s) :
    rotationCLM s (θ + φ) u = rotationCLM s θ (rotationCLM s φ u) := by
  apply coeff_injective s
  funext n
  simp only [coeff_rotationCLM, AddCircle.coe_add, fourier_argument_add]
  ring

@[simp] theorem rotationCLM_zero (s : ℝ) (u : Space s) : rotationCLM s 0 u = u := by
  apply coeff_injective s
  funext n
  simp [coeff_rotationCLM]

theorem norm_rotationCLM_le (s θ : ℝ) (u : Space s) : ‖rotationCLM s θ u‖ ≤ ‖u‖ := by
  simpa only [one_mul, rotationCLM, multiplierCLM, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk] using norm_multiplier_le (s := s) (t := s)
    (fun n => fourier n (θ : AddCircle (2 * Real.pi)))
    (show (0 : ℝ) ≤ 1 by norm_num) (rotationSymbol_bound s θ) u

@[simp] theorem norm_rotationCLM (s θ : ℝ) (u : Space s) : ‖rotationCLM s θ u‖ = ‖u‖ := by
  apply le_antisymm (norm_rotationCLM_le s θ u)
  have h := norm_rotationCLM_le s (-θ) (rotationCLM s θ u)
  rw [← rotationCLM_add, neg_add_cancel, rotationCLM_zero] at h
  exact h

/-- The coefficient action is the existing geometric L2 rotation wherever realization exists. -/
theorem toL2_rotationCLM {s : ℝ} (hs : 0 ≤ s) (θ : ℝ) (u : Space s) :
    toL2 hs (rotationCLM s θ u) = boundaryRotation θ (toL2 hs u) := by
  apply circleFourierCLE.injective
  apply Subtype.ext
  funext n
  rw [circleFourierCLE_boundaryRotation]
  simp only [circleFourierCLE_apply, fourierCoeff_toL2, coeff_rotationCLM]

/-- The paper's character support is the rotation eigenspace at every real order. -/
theorem mem_character_iff_rotationCLM (s : ℝ) (k : ℕ) (hk : 0 < k)
    (j : ℤ) (u : Space s) :
    u ∈ character s j (k : ℤ) ↔
      rotationCLM s (-(2 * Real.pi) / k) u = KsIndex.FormIndex.zeta k ^ j • u := by
  rw [mem_character]
  constructor
  · intro hu
    apply coeff_injective s
    funext n
    rw [coeff_rotationCLM, fourier_rotUnit_angle k hk]
    have hc : coeff s (KsIndex.FormIndex.zeta k ^ j • u) n =
        KsIndex.FormIndex.zeta k ^ j * coeff s u n := by
      exact (coeffLinear s n).map_smul _ _
    rw [hc]
    by_cases hn : ∃ m : ℤ, n = -j + (k : ℤ) * m
    · rw [(zeta_neg_eq_iff k hk j n).mpr hn]
    · rw [hu n hn, mul_zero, mul_zero]
  · intro he n hn
    have h := congrArg (fun v : Space s => coeff s v n) he
    rw [coeff_rotationCLM, fourier_rotUnit_angle k hk] at h
    have hc : coeff s (KsIndex.FormIndex.zeta k ^ j • u) n =
        KsIndex.FormIndex.zeta k ^ j * coeff s u n := by
      exact (coeffLinear s n).map_smul _ _
    rw [hc] at h
    have hz : KsIndex.FormIndex.zeta k ^ (-n) ≠ KsIndex.FormIndex.zeta k ^ j :=
      fun hz => hn ((zeta_neg_eq_iff k hk j n).mp hz)
    exact (mul_eq_zero.mp (show (KsIndex.FormIndex.zeta k ^ (-n) -
      KsIndex.FormIndex.zeta k ^ j) * coeff s u n = 0 by
      rw [sub_mul, h, sub_self])).resolve_left (sub_ne_zero.mpr hz)

/-- Rotation respects the coefficient-preserving Sobolev inclusions. -/
theorem inclusion_rotationCLM {s t : ℝ} (h : t ≤ s) (θ : ℝ) (u : Space s) :
    inclusion h (rotationCLM s θ u) = rotationCLM t θ (inclusion h u) := by
  apply coeff_injective t
  funext n
  simp only [coeff_inclusion, coeff_rotationCLM]

/-- The mean-zero constraint is rotation invariant, at every real order. -/
theorem rotationCLM_mem_dotted_iff (s θ : ℝ) (u : Space s) :
    rotationCLM s θ u ∈ dotted s ↔ u ∈ dotted s := by
  simp only [mem_dotted, coeff_rotationCLM, fourier_zero, one_mul]

/-- Rotation is an invertible complex-linear isometry, not just a bounded map. -/
def rotationEquiv (s θ : ℝ) : Space s ≃ₗᵢ[ℂ] Space s where
  toLinearEquiv :=
    { (rotationCLM s θ).toLinearMap with
      invFun := rotationCLM s (-θ)
      left_inv := fun u => by
        change rotationCLM s (-θ) (rotationCLM s θ u) = u
        rw [← rotationCLM_add, neg_add_cancel, rotationCLM_zero]
      right_inv := fun u => by
        change rotationCLM s θ (rotationCLM s (-θ) u) = u
        rw [← rotationCLM_add, add_neg_cancel, rotationCLM_zero] }
  norm_map' := norm_rotationCLM s θ

end KsIndex.CircleSobolev
