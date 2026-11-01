module

public import KsIndexLean.AlphaFourModeCauchy
public import KsIndexLean.AlphaFourModeReduction

@[expose] public section


/-! Pairing the four retained Fourier outputs against a complex vector. -/
noncomputable section
namespace KsIndex.AlphaFourMode
open CircleQ SIsometry

lemma chat_kernel (i : Fin 4) (n : ℤ) :
    chat (mode i - n) = (2/Real.pi) * kernel i n := by
  unfold chat kernel
  push_cast
  ring

def pairingKernel (a : Fin 4 → ℂ) (n : ℤ) : ℂ :=
  ((2/Real.pi : ℝ) : ℂ) * mixedKernel a n

lemma pairingKernel_eq (a : Fin 4 → ℂ) (n : ℤ) :
    pairingKernel a n = ∑ i, a i * (chat (mode i-n) : ℂ) := by
  simp only [pairingKernel, mixedKernel, Finset.mul_sum, chat_kernel, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma gramEnergy_summable (a : Fin 4 → ℂ) : Summable (gramEnergy a) := by
  apply (integer_sum_split_64 ?_ ?_).1
  · simpa using gramEnergy_shift_summable a 1 (Or.inl rfl)
  · simpa using gramEnergy_shift_summable a (-1) (Or.inr rfl)

lemma pairingEnergy_eq (a : Fin 4 → ℂ) (n : ℤ) :
    ‖pairingKernel a n‖^2 / weight n = (2/Real.pi)^2 * gramEnergy a n := by
  simp only [pairingKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    gramEnergy]
  ring

lemma weightEnergy_summable {u : ℤ → ℂ} (hu : MemDom u) :
    Summable (fun n => weight n * ‖u n‖^2) := by
  simpa only [weight, add_mul] using
    (summable_sigP_mul hu.1).add ((summable_normSq hu.1).mul_left (363/16))

lemma pairing_tsum {u : ℤ → ℂ} (hu : MemDom u) (a : Fin 4 → ℂ) :
    (∑' n, pairingKernel a n * u n) = ∑ i, a i * convS u (mode i) := by
  have hs (i : Fin 4) : Summable (fun n : ℤ => (chat (mode i-n) : ℂ) * u n) :=
    summable_convK_term Sker_row (summable_normSq hu.1) (mode i)
  simp only [pairingKernel_eq, Finset.sum_mul, mul_assoc]
  rw [(summable_tsum_finset_sum Finset.univ _ (fun i _ => (hs i).mul_left (a i))).2]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [convS, tsum_mul_left, mul_assoc]

lemma pairing_cauchy {u : ℤ → ℂ} (hu : MemDom u) (a : Fin 4 → ℂ) :
    ‖∑ i, a i * convS u (mode i)‖^2 ≤
      ((2/Real.pi)^2 * ∑' n, gramEnergy a n) * ∑' n, weight n * ‖u n‖^2 := by
  have hs : Summable (fun n => ‖pairingKernel a n‖^2 / weight n) := by
    simpa only [pairingEnergy_eq] using (gramEnergy_summable a).mul_left ((2/Real.pi)^2)
  have hc := weighted_complex_cauchy (pairingKernel a) u weight weight_pos hs
    (weightEnergy_summable hu)
  rw [pairing_tsum hu a] at hc
  simpa only [pairingEnergy_eq, tsum_mul_left] using hc

end KsIndex.AlphaFourMode
