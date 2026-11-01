module

public import KsIndexLean.HalfDiskExtensional

@[expose] public section


/-! Linear operations on bounded classical half-disk data. -/
noncomputable section
open Set Filter Topology
namespace KsIndex.Trace.ClassicalHalfDiskJacobi
open KsIndex.Surface
variable {k : ℕ} {b : Bool}

def zeroData (k : ℕ) (b : Bool) : ClassicalHalfDiskJacobi k b where
  value := 0
  smooth := contDiffOn_const
  bounded := ⟨0,fun _ _ _ => by simp⟩
  equation := by intro w hw; simp [laplacian]
  boundary := by
    intro w hw hp
    refine ⟨0,contDiffAt_const,Filter.Eventually.of_forall (fun _ _ => rfl),?_⟩
    cases b <;> simp

def addData (u v : ClassicalHalfDiskJacobi k b) : ClassicalHalfDiskJacobi k b where
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
    obtain ⟨F,hF,hs,hB⟩ := u.boundary w hw hp
    obtain ⟨G,hG,ht,hC⟩ := v.boundary w hw hp
    refine ⟨F+G,hF.add hG,?_,?_⟩
    · filter_upwards [hs,ht] with z hz hz'
      intro hn
      simp only [Pi.add_apply,hz hn,hz' hn]
    · cases b
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

def smulData (a : ℂ) (u : ClassicalHalfDiskJacobi k b) : ClassicalHalfDiskJacobi k b where
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
    obtain ⟨F,hF,hs,hB⟩ := u.boundary w hw hp
    refine ⟨a • F,hF.const_smul a,?_,?_⟩
    · filter_upwards [hs] with z hz
      intro hn
      simp only [Pi.smul_apply,hz hn]
    · cases b
      · change F w = 0 at hB
        change a • F w = 0
        rw [hB,smul_zero]
      · change fderiv ℝ (a • F) w w = 0
        rw [((hF.differentiableAt (by simp)).hasFDerivAt.const_smul a).fderiv]
        change fderiv ℝ F w w = 0 at hB
        change a • fderiv ℝ F w w = 0
        rw [hB,smul_zero]

end KsIndex.Trace.ClassicalHalfDiskJacobi
