module

public import KsIndexLean.AlphaGroupAnchorIntervals

@[expose] public section


/-! One forward step from the certified mode-1024 anchors. -/
namespace KsIndex.PowerArc

theorem forwardAnchor_b15 :
    (-441807651372963241849577/40000000000000000000000000000 : ℝ) ≤
      compensatedPowerArcGroup (2161809/5000000 : ℝ) 15
      (2*(12387581/10000000 : ℝ)^2/Real.pi)
      (1+(12387581/10000000 : ℝ)^2) 1025 ∧
    compensatedPowerArcGroup (2161809/5000000 : ℝ) 15
      (2*(12387581/10000000 : ℝ)^2/Real.pi)
      (1+(12387581/10000000 : ℝ)^2) 1025 ≤ (-2761242898148566208524661/250000000000000000000000000000 : ℝ) := by
  have hg := abs_le.mp anchorGroup_b15_error
  have hd := abs_le.mp anchorCorrection_b15_error
  have he := compensatedPowerArcGroup_step (2161809/5000000 : ℝ) 15
      (2*(12387581/10000000 : ℝ)^2/Real.pi)
      (1+(12387581/10000000 : ℝ)^2) 1024
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at he hg hd ⊢
  constructor <;> linarith

theorem forwardAnchor_b14 :
    (-16649393537180759041457/1000000000000000000000000000000 : ℝ) ≤
      compensatedPowerArcGroup (2161809/5000000 : ℝ) 14
      (2*(12387581/10000000 : ℝ)^2/Real.pi)
      (1+(12387581/10000000 : ℝ)^2) 1025 ∧
    compensatedPowerArcGroup (2161809/5000000 : ℝ) 14
      (2*(12387581/10000000 : ℝ)^2/Real.pi)
      (1+(12387581/10000000 : ℝ)^2) 1025 ≤ (-4107425414176722587793/250000000000000000000000000000 : ℝ) := by
  have hg := abs_le.mp anchorGroup_b14_error
  have hd := abs_le.mp anchorCorrection_b14_error
  have he := compensatedPowerArcGroup_step (2161809/5000000 : ℝ) 14
      (2*(12387581/10000000 : ℝ)^2/Real.pi)
      (1+(12387581/10000000 : ℝ)^2) 1024
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at he hg hd ⊢
  constructor <;> linarith

theorem forwardAnchor_c15 :
    (14809468441939931196431/1000000000000000000000000000000 : ℝ) ≤
      compensatedPowerArcGroup (2838191/5000000 : ℝ) 15
      (2*(12387581/10000000 : ℝ)^2/Real.pi)
      (1+(12387581/10000000 : ℝ)^2) 1025 ∧
    compensatedPowerArcGroup (2838191/5000000 : ℝ) 15
      (2*(12387581/10000000 : ℝ)^2/Real.pi)
      (1+(12387581/10000000 : ℝ)^2) 1025 ≤ (3757282770018199080363/250000000000000000000000000000 : ℝ) := by
  have hg := abs_le.mp anchorGroup_c15_error
  have hd := abs_le.mp anchorCorrection_c15_error
  have he := compensatedPowerArcGroup_step (2838191/5000000 : ℝ) 15
      (2*(12387581/10000000 : ℝ)^2/Real.pi)
      (1+(12387581/10000000 : ℝ)^2) 1024
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at he hg hd ⊢
  constructor <;> linarith

theorem forwardAnchor_c14 :
    (2091570950631087256342341/500000000000000000000000000000 : ℝ) ≤
      compensatedPowerArcGroup (2838191/5000000 : ℝ) 14
      (2*(12387581/10000000 : ℝ)^2/Real.pi)
      (1+(12387581/10000000 : ℝ)^2) 1025 ∧
    compensatedPowerArcGroup (2838191/5000000 : ℝ) 14
      (2*(12387581/10000000 : ℝ)^2/Real.pi)
      (1+(12387581/10000000 : ℝ)^2) 1025 ≤ (2091680782032588442786441/500000000000000000000000000000 : ℝ) := by
  have hg := abs_le.mp anchorGroup_c14_error
  have hd := abs_le.mp anchorCorrection_c14_error
  have he := compensatedPowerArcGroup_step (2838191/5000000 : ℝ) 14
      (2*(12387581/10000000 : ℝ)^2/Real.pi)
      (1+(12387581/10000000 : ℝ)^2) 1024
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at he hg hd ⊢
  constructor <;> linarith

end KsIndex.PowerArc
