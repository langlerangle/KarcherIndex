module
public import KsIndexLean.AlphaEnergy4096FiniteBounds
public import KsIndexLean.AlphaEnergy4096SampleTails
@[expose] public section
namespace KsIndex.AlphaRemarkTrial.EnergyWindow4096
open CircleQ
set_option maxRecDepth 10000
theorem qform_lower : (1434/1000000000 : ℝ) ≤ Qform (12387581/10000000) trial := by
  have hp := Energy4096Rows.Pplus.sample_tail_interval.2.1
  have hn := Energy4096Rows.Pminus.sample_tail_interval.2.1
  have hm := Energy4096Rows.Mplus.sample_tail_interval.2.1
  have hj := Energy4096Rows.Mminus.sample_tail_interval.2.1
  have ht := add_le_add (add_le_add hp hn)
    (mul_le_mul_of_nonneg_left (add_le_add hm hj) (sq_nonneg (12387581/10000000 : ℝ)))
  have hf := finite_lower (12387581/10000000)
  have h := add_le_add hf ht
  change _ ≤ _ at h
  rw [qform_eq_finite_add_tails]
  unfold tails
  norm_num at h ⊢
  linarith
#print axioms qform_lower
theorem qform_upper : (-69/1000000000 : ℝ) ≥ Qform (12387574/10000000) trial := by
  have hp := Energy4096Rows.Pplus.sample_tail_interval.2.2
  have hn := Energy4096Rows.Pminus.sample_tail_interval.2.2
  have hm := Energy4096Rows.Mplus.sample_tail_interval.2.2
  have hj := Energy4096Rows.Mminus.sample_tail_interval.2.2
  have ht := add_le_add (add_le_add hp hn)
    (mul_le_mul_of_nonneg_left (add_le_add hm hj) (sq_nonneg (12387574/10000000 : ℝ)))
  have hf := finite_upper (12387574/10000000)
  have h := add_le_add hf ht
  change _ ≤ _ at h
  rw [qform_eq_finite_add_tails]
  unfold tails
  norm_num at h ⊢
  linarith
#print axioms qform_upper
end KsIndex.AlphaRemarkTrial.EnergyWindow4096
