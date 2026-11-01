module

public import KsIndexLean.AlphaTrialResidualSplit
public import KsIndexLean.AlphaTrialReflection
public import KsIndexLean.AlphaInnerPairAssembly

@[expose] public section


/-! Reflected pairing and finite-window decomposition of the actual trial residual. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open CircleQ AlphaResidual

def transposeTerm (n m : ℤ) : ℝ := sigM m * chat (m-n) * (convS trial m).re

def pairedTransposeTerm (n : ℤ) (t : ℕ) : ℝ :=
  transposeTerm n t + transposeTerm n (-(t:ℤ)-1)

lemma pairedTransposeTerm_eq (n : ℤ) (t : ℕ) :
    pairedTransposeTerm n t = (2/Real.pi) * (-1 : ℝ)^((t:ℤ)-n) *
      innerPair n (2*(t:ℝ)+1) (convolutionA t) (convolutionB t) := by
  have hz : (-1 : ℝ)^(-(t:ℤ)-1-n) = -(-1 : ℝ)^((t:ℤ)-n) := by
    have ho : Odd (-2*(t:ℤ)-1) := ⟨-(t:ℤ)-1, by ring⟩
    rw [show -(t:ℤ)-1-n = ((t:ℤ)-n)+(-2*(t:ℤ)-1) by ring,
      zpow_add₀ (by norm_num), ho.neg_one_zpow]
    ring
  have he := reflected_symbol_innerPair n (t:ℤ) (by exact_mod_cast Nat.zero_le t)
    (convolutionA t) (convolutionB t)
  simp only [Int.cast_natCast] at he
  rw [← he]
  unfold pairedTransposeTerm transposeTerm
  rw [convS_trial_re_eq_families, convS_trial_re_eq_families,
    convolutionA_reflect, convolutionB_reflect]
  unfold chat
  rw [hz]
  push_cast
  rw [show 2*(-(t:ℝ)-1-(n:ℝ))+1 = -(2*(t:ℝ)+1+2*(n:ℝ)) by ring,
    show 2*((t:ℝ)-(n:ℝ))+1 = 2*(t:ℝ)+1-2*(n:ℝ) by ring]
  simp only [div_neg]
  ring

lemma summable_transposeTerm (n : ℤ) : Summable (transposeTerm n) :=
  OppositeHalf.summable_transpose OppositeHalf.summable_abs_convS_trial_re n

lemma summable_pairedTransposeTerm (n : ℤ) : Summable (pairedTransposeTerm n) := by
  have h := summable_transposeTerm n
  exact (h.comp_injective (fun a b h => by exact Int.ofNat_injective h)).add
    (h.comp_injective (fun a b h => by dsimp at h; omega : Function.Injective (fun t : ℕ => -(t:ℤ)-1)))

/-- The two reflected half-lines exhaust the transpose series. -/
theorem transpose_eq_paired (n : ℤ) :
    (∑' m : ℤ, transposeTerm n m) = ∑' t : ℕ, pairedTransposeTerm n t := by
  have h := summable_transposeTerm n
  have hp : Summable (fun t : ℕ => transposeTerm n (t:ℤ)) := h.comp_injective (fun a b h => by exact Int.ofNat_injective h : Function.Injective (fun t : ℕ => (t:ℤ)))
  have hm : Summable (fun t : ℕ => transposeTerm n (-((t:ℤ)+1))) := h.comp_injective (fun a b h => by dsimp at h; omega : Function.Injective (fun t : ℕ => -((t:ℤ)+1)))
  rw [tsum_of_nat_of_neg_add_one hp hm, ← Summable.tsum_add hp hm]
  apply tsum_congr
  intro t
  simp only [pairedTransposeTerm, neg_add, sub_eq_add_neg]

/-- A window of T pairs contains precisely m=-T,...,T-1. -/
theorem realResidual_finite_paired (s : ℝ) (n : ℤ) (T : ℕ) :
    realResidual s n = sigP n * (trial n).re + s^2 *
      ((∑ t ∈ Finset.range T, pairedTransposeTerm n t) +
        ∑' k : ℕ, pairedTransposeTerm n (k+T)) := by
  change sigP n * (trial n).re + s^2 * (∑' m, transposeTerm n m) = _
  rw [transpose_eq_paired, ← (summable_pairedTransposeTerm n).sum_add_tsum_nat_add T]

/-- The two families separately have convergent absolute sums. -/
lemma summable_convolution_families : Summable convolutionA ∧ Summable convolutionB := by
  have hv := OppositeHalf.summable_abs_convS_trial_re.of_abs
  have hr := hv.comp_injective (fun a b h => by dsimp at h; omega :
    Function.Injective (fun m : ℤ => -m-1))
  constructor
  · have hh := (hv.sub hr).div_const 2
    apply hh.congr
    intro m
    simp only [Function.comp_def, convS_trial_re_eq_families,
      convolutionA_reflect, convolutionB_reflect]
    ring
  · have hh := (hv.add hr).div_const 2
    apply hh.congr
    intro m
    simp only [Function.comp_def, convS_trial_re_eq_families,
      convolutionA_reflect, convolutionB_reflect]
    ring

end KsIndex.AlphaRemarkTrial
