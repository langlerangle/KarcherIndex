module

public import KsIndexLean.MixedBoundaryCharacter

@[expose] public section


/-! Linear operations on bounded classical half-disk data. -/
noncomputable section
open Set Filter Topology
namespace KsIndex.Trace.ClassicalMixedHalfDiskJacobi
open KsIndex.Surface
variable {k : ℕ} {b1 b0 : Bool}

def zeroData (k : ℕ) (b1 b0 : Bool) : ClassicalMixedHalfDiskJacobi k b1 b0 where
  value := 0
  smooth := contDiffOn_const
  bounded := ⟨0,fun _ _ _ => by simp⟩
  equation := by intro w hw; simp [laplacian]
  boundary := by
    intro w hw hp
    refine ⟨0,contDiffAt_const,Filter.Eventually.of_forall (fun _ _ => rfl),?_,?_⟩
    · intro _; cases b1 <;> simp
    · intro _; cases b0 <;> simp

def addData (u v : ClassicalMixedHalfDiskJacobi k b1 b0) : ClassicalMixedHalfDiskJacobi k b1 b0 where
  value := u.value + v.value
  smooth := u.smooth.add v.smooth
  bounded := by
    obtain ⟨C,hC⟩ := u.bounded
    obtain ⟨D,hD⟩ := v.bounded
    exact ⟨C+D,fun w hw hp => (norm_add_le _ _).trans (add_le_add (hC w hw hp) (hD w hw hp))⟩
  equation := by
    intro w hw
    rw [laplacian_add (u.smooth.contDiffAt (Metric.isOpen_ball.mem_nhds hw))
      (v.smooth.contDiffAt (Metric.isOpen_ball.mem_nhds hw))]
    change _ + (potV k w : ℂ) * (u.value w + v.value w) = 0
    linear_combination u.equation w hw + v.equation w hw
  boundary := by
    intro w hw hp
    obtain ⟨F,hF,hs,hB1,hB0⟩ := u.boundary w hw hp
    obtain ⟨G,hG,ht,hC1,hC0⟩ := v.boundary w hw hp
    refine ⟨F+G,hF.add hG,?_,?_,?_⟩
    · filter_upwards [hs,ht] with z hz hz'
      intro hn
      simp only [Pi.add_apply,hz hn,hz' hn]
    · intro hw1
      have hB := hB1 hw1
      have hC := hC1 hw1
      cases b1
      · change F w = 0 at hB
        change G w = 0 at hC
        change F w + G w = 0
        rw [hB,hC,add_zero]
      · change fderiv ℝ (F+G) w w = 0
        rw [fderiv_add (hF.differentiableAt (by simp)) (hG.differentiableAt (by simp))]
        change fderiv ℝ F w w = 0 at hB
        change fderiv ℝ G w w = 0 at hC
        change fderiv ℝ F w w + fderiv ℝ G w w = 0
        rw [hB,hC,add_zero]
    · intro hw0
      have hB := hB0 hw0
      have hC := hC0 hw0
      cases b0
      · change F w = 0 at hB
        change G w = 0 at hC
        change F w + G w = 0
        rw [hB,hC,add_zero]
      · change fderiv ℝ (F+G) w w = 0
        rw [fderiv_add (hF.differentiableAt (by simp)) (hG.differentiableAt (by simp))]
        change fderiv ℝ F w w = 0 at hB
        change fderiv ℝ G w w = 0 at hC
        change fderiv ℝ F w w + fderiv ℝ G w w = 0
        rw [hB,hC,add_zero]

def smulData (a : ℂ) (u : ClassicalMixedHalfDiskJacobi k b1 b0) : ClassicalMixedHalfDiskJacobi k b1 b0 where
  value := a • u.value
  smooth := u.smooth.const_smul a
  bounded := by
    obtain ⟨C,hC⟩ := u.bounded
    refine ⟨‖a‖*C,fun w hw hp => ?_⟩
    simp only [Pi.smul_apply,norm_smul]
    exact mul_le_mul_of_nonneg_left (hC w hw hp) (norm_nonneg a)
  equation := by
    intro w hw
    rw [laplacian_smul a (u.smooth.contDiffAt (Metric.isOpen_ball.mem_nhds hw))]
    change a * _ + (potV k w : ℂ) * (a * u.value w) = 0
    linear_combination a * u.equation w hw
  boundary := by
    intro w hw hp
    obtain ⟨F,hF,hs,hB1,hB0⟩ := u.boundary w hw hp
    refine ⟨a • F,hF.const_smul a,?_,?_,?_⟩
    · filter_upwards [hs] with z hz
      intro hn
      simp only [Pi.smul_apply,hz hn]
    · intro hw1
      have hB := hB1 hw1
      cases b1
      · change F w = 0 at hB
        change a • F w = 0
        rw [hB,smul_zero]
      · change fderiv ℝ (a • F) w w = 0
        rw [((hF.differentiableAt (by simp)).hasFDerivAt.const_smul a).fderiv]
        change fderiv ℝ F w w = 0 at hB
        change a • fderiv ℝ F w w = 0
        rw [hB,smul_zero]
    · intro hw0
      have hB := hB0 hw0
      cases b0
      · change F w = 0 at hB
        change a • F w = 0
        rw [hB,smul_zero]
      · change fderiv ℝ (a • F) w w = 0
        rw [((hF.differentiableAt (by simp)).hasFDerivAt.const_smul a).fderiv]
        change fderiv ℝ F w w = 0 at hB
        change a • fderiv ℝ F w w = 0
        rw [hB,smul_zero]

end KsIndex.Trace.ClassicalMixedHalfDiskJacobi

#print axioms KsIndex.Trace.ClassicalMixedHalfDiskJacobi.zeroData
#print axioms KsIndex.Trace.ClassicalMixedHalfDiskJacobi.addData
#print axioms KsIndex.Trace.ClassicalMixedHalfDiskJacobi.smulData
