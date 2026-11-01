module

public import KsIndexLean.AlphaTrialResidualSplit
public import KsIndexLean.AlphaOppositeHalfGroups
public import KsIndexLean.PowerArcStieltjesRecurrence

@[expose] public section


/-! Exact Stieltjes representations of the actual trial's signed moment tails. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open CircleQ PowerArc OppositeHalf

lemma summable_signed_stieltjes {β r z : ℝ} (hβ : 0 < β) (hr : β ≤ r) (hz : 0 < z) :
    Summable (fun k : ℕ => (-1 : ℝ)^k * g β (r+2*k) / ((k:ℝ)+z)) := by
  apply summable_div_nat_add (z := z) ?_ hz
  apply Summable.of_abs
  simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using abs_g_summable hβ hr

/-- Upper half-line moment, with the parity and factor of six kept separate. -/
theorem momentKa_trial : momentKa (fun m => (convS trial m).re) =
    ∑ i : Fin 25, ((coefficient i).re / g (exponent i) 0) *
      powerArcStieltjes (exponent i) (9+shift i) (14/3) := by
  have hsum (i : Fin 25) : Summable (fun k : ℕ =>
      (-1 : ℝ)^k * g (exponent i) ((9+shift i)+2*k) / ((k:ℝ)+14/3)) := by
    apply summable_signed_stieltjes (exponent_pos i) ?_ (by norm_num)
    fin_cases i <;> norm_num [exponent, shift]
  unfold momentKa
  have he : (fun k : ℕ => (-1 : ℝ)^k * (convS trial (4+k)).re / ((k:ℝ)+14/3)) =
      fun k : ℕ => ∑ i : Fin 25, ((coefficient i).re / g (exponent i) 0) *
        ((-1 : ℝ)^k * g (exponent i) ((9+shift i)+2*k) / ((k:ℝ)+14/3)) := by
    funext k
    change (-1 : ℝ)^k * vTrial (4+k) / ((k:ℝ)+14/3) = _
    rw [vTrial_eq_sum, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [show 2*((4+(k:ℤ):ℤ):ℝ)+((shift i:ℝ)+1) = (9+shift i)+2*k by push_cast; ring]
    ring
  rw [he, Summable.tsum_finsetSum (fun i _ => (hsum i).mul_left _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [tsum_mul_left, powerArcStieltjes]

/-- Lower half-line moment after reflection. -/
theorem momentKb_trial : momentKb (fun m => (convS trial m).re) =
    ∑ i : Fin 25, ((coefficient i).re / g (exponent i) 0) *
      powerArcStieltjes (exponent i) (9-shift i) (13/3) := by
  unfold momentKb
  have he : (fun k : ℕ => (-1 : ℝ)^k * (convS trial (-5-k)).re / ((k:ℝ)+13/3)) =
      fun k : ℕ => ∑ i : Fin 25, ((coefficient i).re / g (exponent i) 0) *
        ((-1 : ℝ)^k * g (exponent i) ((9-shift i)+2*k) / ((k:ℝ)+13/3)) := by
    funext k
    change (-1 : ℝ)^k * vTrial (-5-k) / ((k:ℝ)+13/3) = _
    rw [vTrial_eq_sum, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [show 2*((-5-(k:ℤ):ℤ):ℝ)+((shift i:ℝ)+1) = -((9-shift i)+2*k) by push_cast; ring, g_neg]
    ring
  rw [he, Summable.tsum_finsetSum (fun i _ =>
    (summable_term_stieltjes i (by norm_num : (0:ℝ)<13/3)).mul_left _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [tsum_mul_left, powerArcStieltjes]

/-- The eight central terms of the signed moment. -/
def trialMomentPrefix : ℝ :=
  (∑ k ∈ Finset.range 4, (-1 : ℝ)^(k : ℤ) * (convS trial (k : ℤ)).re /
    (6*((k : ℤ):ℝ)+4)) +
  ∑ k ∈ Finset.range 4, (-1 : ℝ)^(-((k : ℤ)+1)) * (convS trial (-((k : ℤ)+1))).re /
    (6*((-((k : ℤ)+1):ℤ):ℝ)+4)

/-- The actual shared moment is a finite prefix plus two finite sums of Stieltjes transforms. -/
theorem signedTrialMoment_eq_transforms : signedTrialMoment = trialMomentPrefix +
    ((∑ i : Fin 25, ((coefficient i).re / g (exponent i) 0) *
      powerArcStieltjes (exponent i) (9+shift i) (14/3)) +
     (∑ i : Fin 25, ((coefficient i).re / g (exponent i) 0) *
      powerArcStieltjes (exponent i) (9-shift i) (13/3))) / 6 := by
  rw [signedTrialMoment, tsum_V_split summable_abs_convS_trial_re,
    momentKa_trial, momentKb_trial]
  rfl

end KsIndex.AlphaRemarkTrial
