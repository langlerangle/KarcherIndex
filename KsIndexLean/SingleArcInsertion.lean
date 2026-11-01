module

public import KsIndexLean.SingleArcReindex

@[expose] public section


noncomputable section
namespace KsIndex.SingleArcReindex
open ModeWitness CircleSobolev

/-- Insert physical coefficients on the class lattice and put zero elsewhere. -/
def insertCoeff (k j : ℕ) (a : ℤ → ℂ) : ℤ → ℂ :=
  Function.extend (lz k j) a 0

@[simp] lemma insertCoeff_lattice {k : ℕ} (hk : 3 ≤ k) (j : ℕ)
    (a : ℤ → ℂ) (n : ℤ) : insertCoeff k j a (lz k j n) = a n :=
  (lz_injective (r := j) hk).extend_apply a 0 n

lemma insertCoeff_off (k j : ℕ) (a : ℤ → ℂ) (m : ℤ)
    (hm : ¬ ∃ n, m = lz k j n) : insertCoeff k j a m = 0 := by
  apply Function.extend_apply'
  simpa only [eq_comm] using hm

lemma insertion_summable {k : ℕ} (hk : 3 ≤ k) (j : ℕ)
    (f : Space (1 / 2)) :
    Summable (fun m => weight (1 / 2) m ^ 2 *
      ‖insertCoeff k j (coeff (1 / 2) f) m‖ ^ 2) := by
  have h := (hasSum_weighted_sq (1 / 2) f).summable.mul_left ((k : ℝ) + 1)
  have hs : Summable (fun n => weight (1 / 2) (lz k j n) ^ 2 *
      ‖coeff (1 / 2) f n‖ ^ 2) := by
    refine h.of_nonneg_of_le (fun n => by positivity) fun n => ?_
    have hw (m : ℤ) : weight (1 / 2) m ^ 2 = 1 + |(m : ℝ)| := by
      rw [weight_sq]; norm_num
    simp only [hw]
    nlinarith [mul_le_mul_of_nonneg_right (lattice_weight_upper k j n)
      (sq_nonneg ‖coeff (1 / 2) f n‖)]
  have he := (summable_extend_zero (lz_injective (r := j) hk)).mpr hs
  apply he.congr
  intro m
  by_cases hm : ∃ n, m = lz k j n
  · obtain ⟨n, rfl⟩ := hm
    rw [(lz_injective (r := j) hk).extend_apply, insertCoeff_lattice hk]
  · rw [Function.extend_apply' _ _ _ (by simpa only [eq_comm] using hm),
      insertCoeff_off k j _ m hm]
    simp

/-- Insertion into the actual half-order Sobolev carrier. -/
def insert {k : ℕ} (hk : 3 ≤ k) (j : ℕ) (f : Space (1 / 2)) : Space (1 / 2) :=
  ofCoefficients (1 / 2) (insertCoeff k j (coeff (1 / 2) f))
    (insertion_summable hk j f)

@[simp] lemma coeff_insert {k : ℕ} (hk : 3 ≤ k) (j : ℕ)
    (f : Space (1 / 2)) (m : ℤ) :
    coeff (1 / 2) (insert hk j f) m = insertCoeff k j (coeff (1 / 2) f) m :=
  coeff_ofCoefficients _ _ _ _

lemma insert_mem_character {k j : ℕ} (hk : 3 ≤ k) (hj : j ≤ k)
    (f : Space (1 / 2)) : insert hk j f ∈ character (1 / 2) j k := by
  rw [mem_character]
  intro m hm
  rw [coeff_insert]
  exact insertCoeff_off k j _ m (fun hn => hm ((lattice_range hj m).mp hn))

@[simp] lemma extract_insert {k : ℕ} (hk : 3 ≤ k) (j : ℕ)
    (f : Space (1 / 2)) : extract hk j (insert hk j f) = f := by
  apply coeff_injective (1 / 2)
  funext n
  simp only [coeff_extract, coeff_insert, insertCoeff_lattice hk]

lemma insert_extract {k j : ℕ} (hk : 3 ≤ k) (hj : j ≤ k)
    (f : Space (1 / 2)) (hf : f ∈ character (1 / 2) j k) :
    insert hk j (extract hk j f) = f := by
  apply extract_injective_on_character hk hj (insert_mem_character hk hj _) hf
  exact extract_insert hk j _

end KsIndex.SingleArcReindex
