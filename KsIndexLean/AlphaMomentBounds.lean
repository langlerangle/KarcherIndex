module

public import KsIndexLean.AlphaMomentCancellation
public import KsIndexLean.AlphaMomentLinear
public import KsIndexLean.AlphaMomentPrefixAffine
public import KsIndexLean.AlphaMomentSharedLeaves
public import KsIndexLean.AlphaSeedApproximation

@[expose] public section

noncomputable section
namespace KsIndex.AlphaRemarkTrial
open OppositeHalf PowerArc PowerArc.MomentSeeds
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem Upos_certified : (1885893027939879219892305162102252273141/250000000000000000000000000000000000000 : ℝ) ≤ Upos ∧ Upos ≤ (9429465377652037812387170493739502587577/1250000000000000000000000000000000000000 : ℝ) := by
  have ha := abs_le.mp gamma_seed_approximation
  have hb := abs_le.mp beta_seed_approximation
  have ha0 : 0 ≤ g (2161809/5000000 : ℝ) 1/g (2161809/5000000 : ℝ) 0 := by linarith [ha.1]
  have hb0 : 0 ≤ g (2838191/5000000 : ℝ) 1/g (2838191/5000000 : ℝ) 0 := by linarith [hb.1]
  have h2161809_14_13 := b2161809_r14_z13_shared
  have h2161809_14_13 := abs_le.mp h2161809_14_13
  have h2161809_14_14 := b2161809_r14_z14_shared
  have h2161809_14_14 := abs_le.mp h2161809_14_14
  have h2161809_15_13 := b2161809_r15_z13_shared
  rw [abs_of_nonneg ha0] at h2161809_15_13
  have h2161809_15_13 := abs_le.mp h2161809_15_13
  have h2161809_15_14 := b2161809_r15_z14_shared
  rw [abs_of_nonneg ha0] at h2161809_15_14
  have h2161809_15_14 := abs_le.mp h2161809_15_14
  have h2838191_14_13 := b2838191_r14_z13_shared
  have h2838191_14_13 := abs_le.mp h2838191_14_13
  have h2838191_14_14 := b2838191_r14_z14_shared
  have h2838191_14_14 := abs_le.mp h2838191_14_14
  have h2838191_15_13 := b2838191_r15_z13_shared
  rw [abs_of_nonneg hb0] at h2838191_15_13
  have h2838191_15_13 := abs_le.mp h2838191_15_13
  have h2838191_15_14 := b2838191_r15_z14_shared
  rw [abs_of_nonneg hb0] at h2838191_15_14
  have h2838191_15_14 := abs_le.mp h2838191_15_14
  rw [Upos_eq_cancelled, trialMomentPrefix_affine, reducedMomentLower_linear, reducedMomentUpper_linear]
  constructor <;> linarith only [ha.1, ha.2, hb.1, hb.2, h2161809_14_13.1, h2161809_14_13.2, h2161809_14_14.1, h2161809_14_14.2, h2161809_15_13.1, h2161809_15_13.2, h2161809_15_14.1, h2161809_15_14.2, h2838191_14_13.1, h2838191_14_13.2, h2838191_14_14.1, h2838191_14_14.2, h2838191_15_13.1, h2838191_15_13.2, h2838191_15_14.1, h2838191_15_14.2]

theorem Uneg_certified : (37424396811971859178886210706290858247639/5000000000000000000000000000000000000000 : ℝ) ≤ Uneg ∧ Uneg ≤ (18712198881866272883929107452106957182859/2500000000000000000000000000000000000000 : ℝ) := by
  have ha := abs_le.mp gamma_seed_approximation
  have hb := abs_le.mp beta_seed_approximation
  have ha0 : 0 ≤ g (2161809/5000000 : ℝ) 1/g (2161809/5000000 : ℝ) 0 := by linarith [ha.1]
  have hb0 : 0 ≤ g (2838191/5000000 : ℝ) 1/g (2838191/5000000 : ℝ) 0 := by linarith [hb.1]
  have h2161809_14_13 := b2161809_r14_z13_shared
  have h2161809_14_13 := abs_le.mp h2161809_14_13
  have h2161809_14_14 := b2161809_r14_z14_shared
  have h2161809_14_14 := abs_le.mp h2161809_14_14
  have h2161809_15_13 := b2161809_r15_z13_shared
  rw [abs_of_nonneg ha0] at h2161809_15_13
  have h2161809_15_13 := abs_le.mp h2161809_15_13
  have h2161809_15_14 := b2161809_r15_z14_shared
  rw [abs_of_nonneg ha0] at h2161809_15_14
  have h2161809_15_14 := abs_le.mp h2161809_15_14
  have h2838191_14_13 := b2838191_r14_z13_shared
  have h2838191_14_13 := abs_le.mp h2838191_14_13
  have h2838191_14_14 := b2838191_r14_z14_shared
  have h2838191_14_14 := abs_le.mp h2838191_14_14
  have h2838191_15_13 := b2838191_r15_z13_shared
  rw [abs_of_nonneg hb0] at h2838191_15_13
  have h2838191_15_13 := abs_le.mp h2838191_15_13
  have h2838191_15_14 := b2838191_r15_z14_shared
  rw [abs_of_nonneg hb0] at h2838191_15_14
  have h2838191_15_14 := abs_le.mp h2838191_15_14
  rw [Uneg_eq_cancelled, trialMomentPrefix_affine, reducedMomentLower_linear, reducedMomentUpper_linear]
  constructor <;> linarith only [ha.1, ha.2, hb.1, hb.2, h2161809_14_13.1, h2161809_14_13.2, h2161809_14_14.1, h2161809_14_14.2, h2161809_15_13.1, h2161809_15_13.2, h2161809_15_14.1, h2161809_15_14.2, h2838191_14_13.1, h2838191_14_13.2, h2838191_14_14.1, h2838191_14_14.2, h2838191_15_13.1, h2838191_15_13.2, h2838191_15_14.1, h2838191_15_14.2]

theorem Upos_row_bounds : (75435720375282880992999797257990978336632/10^40 : ℝ) ≤ Upos ∧
    Upos ≤ (75435723763528590617612460575846781620200/10^40 : ℝ) := by
  constructor
  · exact le_trans (by norm_num) Upos_certified.1
  · exact le_trans Upos_certified.2 (by norm_num)

theorem Uneg_row_bounds : (74848792232710618720219264367045728970428/10^40 : ℝ) ≤ Uneg ∧
    Uneg ≤ (74848796918698190857446899454132167925740/10^40 : ℝ) := by
  constructor
  · exact le_trans (by norm_num) Uneg_certified.1
  · exact le_trans Uneg_certified.2 (by norm_num)

end KsIndex.AlphaRemarkTrial
#print axioms KsIndex.AlphaRemarkTrial.Upos_certified
#print axioms KsIndex.AlphaRemarkTrial.Uneg_certified
