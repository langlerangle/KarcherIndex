module

public import KsIndexLean.KaiOuterRawBound
public import KsIndexLean.AlphaMomentBounds

@[expose] public section

noncomputable section
namespace KsIndex.AlphaRemarkTrial
open PowerArc OppositeHalf

theorem rawRemainder_outer_certified :
    ∀ m : ℕ, 1025 < m → |rawRemainder (m : ℝ)| ≤ 1/(m : ℝ) := by
  have ha := abs_le.mp gamma_seed_approximation
  have hb := abs_le.mp beta_seed_approximation
  apply KsIndex.Stage3Outer.rawRemainder_outer_le
    (719689654/1000000000) (719689660/1000000000)
    (738631769/1000000000) (738631773/1000000000)
    (75435720375282880992999797257990978336632/10^40) (75435723763528590617612460575846781620200/10^40)
  all_goals first | exact Upos_row_bounds.1 | exact Upos_row_bounds.2 | (norm_num; done) | linarith [ha.1, ha.2, hb.1, hb.2]

theorem rawRemainderNegative_outer_certified :
    ∀ m : ℕ, 1025 < m → |rawRemainderNegative (m : ℝ)| ≤ 1/(m : ℝ) := by
  have ha := abs_le.mp gamma_seed_approximation
  have hb := abs_le.mp beta_seed_approximation
  apply KsIndex.Stage3Outer.rawRemainderNegative_outer_le
    (719689654/1000000000) (719689660/1000000000)
    (738631769/1000000000) (738631773/1000000000)
    (74848792232710618720219264367045728970428/10^40) (74848796918698190857446899454132167925740/10^40)
  all_goals first | exact Uneg_row_bounds.1 | exact Uneg_row_bounds.2 | (norm_num; done) | linarith [ha.1, ha.2, hb.1, hb.2]

end KsIndex.AlphaRemarkTrial
#print axioms KsIndex.AlphaRemarkTrial.rawRemainder_outer_certified
#print axioms KsIndex.AlphaRemarkTrial.rawRemainderNegative_outer_certified
