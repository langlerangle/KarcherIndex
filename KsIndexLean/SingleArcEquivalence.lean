module

public import KsIndexLean.SingleArcInsertion

@[expose] public section


noncomputable section
namespace KsIndex.SingleArcReindex
open ModeWitness CircleSobolev

private lemma half_weight_sq (m : ℤ) : weight (1 / 2) m ^ 2 = 1 + |(m : ℝ)| := by
  rw [weight_sq]; norm_num

lemma extract_norm_sq_le {k : ℕ} (hk : 3 ≤ k) (j : ℕ) (f : Space (1 / 2)) :
    ‖extract hk j f‖ ^ 2 ≤ 2 * ‖f‖ ^ 2 := by
  rw [← (hasSum_weighted_sq (1 / 2) (extract hk j f)).tsum_eq,
    ← (hasSum_weighted_sq (1 / 2) f).tsum_eq, ← tsum_mul_left]
  apply Summable.tsum_le_tsum_of_inj (lz k j) (lz_injective hk)
    (fun _ _ => by positivity)
  · intro n
    rw [coeff_extract, half_weight_sq, half_weight_sq]
    nlinarith [mul_le_mul_of_nonneg_right
      (lattice_weight_lower (by omega : 1 ≤ k) j n)
      (sq_nonneg ‖coeff (1 / 2) f (lz k j n)‖)]
  · exact (hasSum_weighted_sq _ _).summable
  · exact (hasSum_weighted_sq _ _).summable.mul_left 2

lemma insert_norm_sq_le {k : ℕ} (hk : 3 ≤ k) (j : ℕ) (f : Space (1 / 2)) :
    ‖insert hk j f‖ ^ 2 ≤ ((k : ℝ) + 1) * ‖f‖ ^ 2 := by
  have he : (fun m => weight (1 / 2) m ^ 2 * ‖coeff (1 / 2) (insert hk j f) m‖ ^ 2) =
      Function.extend (lz k j)
        (fun n => weight (1 / 2) (lz k j n) ^ 2 * ‖coeff (1 / 2) f n‖ ^ 2) 0 := by
    funext m
    rw [coeff_insert]
    by_cases hm : ∃ n, m = lz k j n
    · obtain ⟨n, rfl⟩ := hm
      rw [insertCoeff_lattice hk, (lz_injective (r := j) hk).extend_apply]
    · rw [insertCoeff_off k j _ m hm,
        Function.extend_apply' _ _ _ (by simpa only [eq_comm] using hm)]
      simp
  have hs : Summable (fun n => weight (1 / 2) (lz k j n) ^ 2 *
      ‖coeff (1 / 2) f n‖ ^ 2) := by
    apply (summable_extend_zero (lz_injective (r := j) hk)).mp
    rw [← he]
    exact (hasSum_weighted_sq _ _).summable
  rw [← (hasSum_weighted_sq (1 / 2) (insert hk j f)).tsum_eq, he,
    tsum_extend_zero (lz_injective hk), ← (hasSum_weighted_sq (1 / 2) f).tsum_eq,
    ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun n => ?_) hs
    ((hasSum_weighted_sq _ _).summable.mul_left _)
  rw [half_weight_sq, half_weight_sq]
  nlinarith [mul_le_mul_of_nonneg_right (lattice_weight_upper k j n)
    (sq_nonneg ‖coeff (1 / 2) f n‖)]

/-- Algebraic equivalence between the half-order character space and Space (1 / 2). -/
def characterEquiv {k j : ℕ} (hk : 3 ≤ k) (hj : j ≤ k) :
    character (1 / 2) j k ≃ₗ[ℂ] Space (1 / 2) where
  toFun f := extract hk j f.val
  invFun g := ⟨insert hk j g, insert_mem_character hk hj g⟩
  left_inv f := Subtype.ext (insert_extract hk hj f.val f.property)
  right_inv := extract_insert hk j
  map_add' f g := (extractLinear hk j).map_add f.val g.val
  map_smul' c f := (extractLinear hk j).map_smul c f.val

/-- The weight comparison gives continuity in both half-order Sobolev norms. -/
def characterContinuousEquiv {k j : ℕ} (hk : 3 ≤ k) (hj : j ≤ k) :
    character (1 / 2) j k ≃L[ℂ] Space (1 / 2) :=
  (characterEquiv hk hj).toContinuousLinearEquivOfBounds
    (Real.sqrt 2) (Real.sqrt ((k : ℝ) + 1))
    (fun f => by
      have h := extract_norm_sq_le hk j f.val
      change ‖extract hk j f.val‖ ≤ Real.sqrt 2 * ‖f.val‖
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      simpa only [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] using h)
    (fun g => by
      have h := insert_norm_sq_le hk j g
      change ‖insert hk j g‖ ≤ Real.sqrt ((k : ℝ) + 1) * ‖g‖
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      simpa only [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ (k : ℝ) + 1 by positivity)] using h)


end KsIndex.SingleArcReindex
