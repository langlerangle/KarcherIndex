module

public import KsIndexLean.KarcherCenterNormalization
public import KsIndexLean.KarcherLiftSeams

@[expose] public section


/-! Positional normalization of the actual EW map with the paper's height shift. -/
noncomputable section
namespace KsIndex.KarcherData
open Complex
open scoped ContDiff Manifold ParameterAtlas PeriodicAmbient

def paperNormalizedMap {k : ℕ} (hk : 2 ≤ k) (C : PeriodTarget) (t : ℝ)
    (p : ParameterSphere k) : PeriodTarget :=
  (t, 0, (Real.pi : AddCircle (2 * Real.pi))) + extendedEWMap hk (reflectionBasepoint k) C p

lemma rotation_offset_vertical_shift (D T : PeriodTarget) (a : ℂ) (v : AddCircle (2 * Real.pi)) :
    D + (T + (0, 0, v)) - PeriodTarget.rotate a (T + (0, 0, v)) =
      D + T - PeriodTarget.rotate a T := by
  rw [periodRotate_add]
  have hv : PeriodTarget.rotate a (0, 0, v) = (0, 0, v) := by simp [PeriodTarget.rotate]
  rw [hv]
  abel

/-- The horizontal center also normalizes the screw after the π height shift
used in the half-period disk identification. -/
theorem exists_paper_centered_screw {k : ℕ} [h : Fact (2 ≤ k)]
    (C : PeriodTarget) (hF : Continuous (extendedEWMap h.out (reflectionBasepoint k) C))
    (θ : ℝ) (hθ : (Complex.exp (θ * I)) ^ k = -1) :
    ∃ t : ℝ, ∀ p,
      paperNormalizedMap h.out C t (parameterScrew h.out θ hθ p) =
        (0, 0, (Real.pi : AddCircle (2 * Real.pi))) +
          PeriodTarget.rotate (Complex.exp (θ * I)) (paperNormalizedMap h.out C t p) := by
  let β := Complex.exp (θ * I)
  have hβ : β ∉ Surface.punctures k := by
    intro he
    have hh : β ^ (2 * k) = -1 := he
    rw [root_double_of_neg_one hθ] at hh
    norm_num at hh
  have hβ2 : β ^ 2 ∉ Surface.punctures k := by
    intro he
    have hh : (β ^ 2) ^ (2 * k) = -1 := he
    rw [← pow_mul, mul_comm 2 (2 * k), pow_mul, root_double_of_neg_one hθ] at hh
    norm_num at hh
  obtain ⟨t, _, hc⟩ := exists_center_translation h.out hθ (reflectionBasepoint k).property hβ hβ2
  have he : ∀ p, extendedEWMap h.out (reflectionBasepoint k) C (parameterScrew h.out θ hθ p) =
      descendedIntegral h.out (reflectionBasepoint k) ⟨β, hβ⟩ +
        PeriodTarget.rotate β (extendedEWMap h.out (reflectionBasepoint k) C p) := by
    intro p
    simpa only [reflectionBasepoint, map_one, inv_one, mul_one] using
      extendedEWMap_screw θ hθ (reflectionBasepoint k) (by simp [reflectionBasepoint]) C hF p
  have hc' : descendedIntegral h.out (reflectionBasepoint k) ⟨β, hβ⟩ +
      (t, 0, (Real.pi : AddCircle (2 * Real.pi))) -
      PeriodTarget.rotate β (t, 0, (Real.pi : AddCircle (2 * Real.pi))) =
        (0, 0, (Real.pi : AddCircle (2 * Real.pi))) := by
    have hh := rotation_offset_vertical_shift
      (descendedIntegral h.out (reflectionBasepoint k) ⟨β, hβ⟩) (t, 0, 0) β Real.pi
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using hh.trans hc
  exact ⟨t, translated_rotation_identity _ _ β _ _ _ he hc'⟩

lemma periodRotate_square (a : ℂ) (p : PeriodTarget) :
    PeriodTarget.rotate a (PeriodTarget.rotate a p) = PeriodTarget.rotate (a ^ 2) p := by
  ext <;> simp [PeriodTarget.rotate, pow_two, Complex.mul_re, Complex.mul_im] <;> ring

/-- Squaring the centered screw gives the centered full rotation on the same map. -/
theorem centered_screw_rotation {k : ℕ} [h : Fact (2 ≤ k)]
    (F : ParameterSphere k → PeriodTarget) (θ : ℝ)
    (hθ : (Complex.exp (θ * I)) ^ k = -1)
    (hs : ∀ p, F (parameterScrew h.out θ hθ p) =
      (0, 0, (Real.pi : AddCircle (2 * Real.pi))) + PeriodTarget.rotate (Complex.exp (θ * I)) (F p)) :
    ∀ p, F (parameterRotation (θ + θ)
      (phase_root_add (root_double_of_neg_one hθ) (root_double_of_neg_one hθ)) p) =
        PeriodTarget.rotate (Complex.exp (θ * I) ^ 2) (F p) := by
  intro p
  rw [← parameterScrew_square θ hθ p, hs, hs, periodRotate_add, periodRotate_square]
  have hv : PeriodTarget.rotate (Complex.exp (θ * I))
      (0, 0, (Real.pi : AddCircle (2 * Real.pi))) = (0, 0, (Real.pi : AddCircle (2 * Real.pi))) := by
    simp [PeriodTarget.rotate]
  rw [hv, ← add_assoc]
  have hh : ((0, 0, (Real.pi : AddCircle (2 * Real.pi))) : PeriodTarget) +
      (0, 0, (Real.pi : AddCircle (2 * Real.pi))) = 0 := by
    apply Prod.ext (by simp)
    apply Prod.ext (by simp)
    change (Real.pi : AddCircle (2 * Real.pi)) + Real.pi = 0
    rw [← AddCircle.coe_add, show Real.pi + Real.pi = 2 * Real.pi by ring]
    exact AddCircle.coe_period (2 * Real.pi)
  rw [hh, zero_add]

lemma paperNormalizedMap_seam {k : ℕ} [h : Fact (2 ≤ k)] (C : PeriodTarget)
    (hF : Continuous (extendedEWMap h.out (reflectionBasepoint k) C)) (t : ℝ) (p : ParameterSphere k) :
    paperNormalizedMap h.out C t (parameterSeamReflection h.out p) =
      PeriodTarget.reflZ (paperNormalizedMap h.out C t p) := by
  unfold paperNormalizedMap
  rw [based_seam_identity C hF]
  apply Prod.ext (by rfl)
  apply Prod.ext (by rfl)
  change (Real.pi : AddCircle (2 * Real.pi)) + _ = -((Real.pi : AddCircle (2 * Real.pi)) + _)
  rw [neg_add, ← AddCircle.coe_neg, coe_neg_pi_eq_pi]
  rfl

lemma paperNormalizedMap_conjugation {k : ℕ} [h : Fact (2 ≤ k)] (C : PeriodTarget)
    (hF : Continuous (extendedEWMap h.out (reflectionBasepoint k) C)) (t : ℝ) (p : ParameterSphere k) :
    paperNormalizedMap h.out C t (parameterConjugation p) =
      PeriodTarget.reflY (paperNormalizedMap h.out C t p) := by
  have he := extendedEWMap_conjugation (reflectionBasepoint k) C hF p
  have hb : (⟨starRingEnd ℂ (reflectionBasepoint k).val,
      conjugate_not_puncture (reflectionBasepoint k).property⟩ : PuncturedPlane k) = reflectionBasepoint k := by
    apply Subtype.ext
    simp [reflectionBasepoint]
  rw [hb, descendedIntegral_self, zero_add] at he
  unfold paperNormalizedMap
  rw [he]
  simp [PeriodTarget.reflY]

/-- One horizontal center realizes conjugation, seam reflection, the screw at
parameter angle `-π/k`, and rotation at `-2π/k`, after the vertical π shift. -/
theorem exists_paper_positional_symmetries {k : ℕ} [h : Fact (2 ≤ k)]
    (C : PeriodTarget) (hF : Continuous (extendedEWMap h.out (reflectionBasepoint k) C)) :
    ∃ t : ℝ,
      (∀ p, paperNormalizedMap h.out C t (parameterConjugation p) =
        PeriodTarget.reflY (paperNormalizedMap h.out C t p)) ∧
      (∀ p, paperNormalizedMap h.out C t (parameterSeamReflection h.out p) =
        PeriodTarget.reflZ (paperNormalizedMap h.out C t p)) ∧
      (∀ p, paperNormalizedMap h.out C t
          (parameterScrew h.out (-Real.pi / k) (paper_screw_root h.out) p) =
        (0, 0, (Real.pi : AddCircle (2 * Real.pi))) +
          PeriodTarget.rotate (Complex.exp ((-Real.pi / k : ℝ) * I))
            (paperNormalizedMap h.out C t p)) ∧
      (∀ p, paperNormalizedMap h.out C t
          (parameterRotation (-2 * Real.pi / k)
            (by rw [two_mul, pow_add, paper_rotation_root h.out, one_mul]) p) =
        PeriodTarget.rotate (Complex.exp ((-2 * Real.pi / k : ℝ) * I))
          (paperNormalizedMap h.out C t p)) := by
  obtain ⟨t, hs⟩ := exists_paper_centered_screw C hF (-Real.pi / k) (paper_screw_root h.out)
  refine ⟨t, paperNormalizedMap_conjugation C hF t, paperNormalizedMap_seam C hF t, hs, ?_⟩
  have hr := centered_screw_rotation (paperNormalizedMap h.out C t)
    (-Real.pi / k) (paper_screw_root h.out) hs
  have ha : (-Real.pi / k : ℝ) + (-Real.pi / k) = -2 * Real.pi / k := by ring
  have hb : Complex.exp ((-Real.pi / k : ℝ) * I) ^ 2 =
      Complex.exp ((-2 * Real.pi / k : ℝ) * I) := by
    rw [pow_two, ← phase_add, ha]
  simpa only [ha, hb] using hr

/-- An EW extension with a horizontal center, smooth connected covering,
half-period disk bijection, and positional symmetries for the same map. -/
structure PaperHalfPeriodRealization (k : ℕ) [h : Fact (2 ≤ k)] where
  C : PeriodTarget
  hC : Continuous (extendedEWMap h.out (reflectionBasepoint k) C)
  t : ℝ
  connected : PathConnectedSpace (PeriodicEWCarrier h.out (reflectionBasepoint k) C)
  geometry :
    letI := HeightLift.liftChartedSpace hC
    IsManifold 𝓘(ℝ, ℂ) ∞ (PeriodicEWCarrier h.out (reflectionBasepoint k) C) ∧
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) ∞
        (HeightLift.ambient (F := extendedEWMap h.out (reflectionBasepoint k) C)) ∧
      (∀ q : PeriodicEWCarrier h.out (reflectionBasepoint k) C,
        IsDiffImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) HeightLift.ambient q)
  covering : IsCoveringMap (HeightLift.projection (F := extendedEWMap h.out (reflectionBasepoint k) C))
  diskMap : PaperHalfPeriod h.out (reflectionBasepoint k) C → PuncturedClosedDisk k
  projection_agrees : ∀ q, finiteParameter (diskMap q).val = HeightLift.projection q.val
  disk_bijective : Function.Bijective diskMap
  symmetries :
      (∀ p, paperNormalizedMap h.out C t (parameterConjugation p) =
        PeriodTarget.reflY (paperNormalizedMap h.out C t p)) ∧
      (∀ p, paperNormalizedMap h.out C t (parameterSeamReflection h.out p) =
        PeriodTarget.reflZ (paperNormalizedMap h.out C t p)) ∧
      (∀ p, paperNormalizedMap h.out C t
          (parameterScrew h.out (-Real.pi / k) (paper_screw_root h.out) p) =
        (0, 0, (Real.pi : AddCircle (2 * Real.pi))) +
          PeriodTarget.rotate (Complex.exp ((-Real.pi / k : ℝ) * I))
            (paperNormalizedMap h.out C t p)) ∧
      (∀ p, paperNormalizedMap h.out C t
          (parameterRotation (-2 * Real.pi / k)
            (by rw [two_mul, pow_add, paper_rotation_root h.out, one_mul]) p) =
        PeriodTarget.rotate (Complex.exp ((-2 * Real.pi / k : ℝ) * I))
          (paperNormalizedMap h.out C t p))

/-- For every `k ≥ 2`, the EW construction supplies a realization, including
its connectedness, smooth immersion, covering, disk bijection, and symmetries. -/
theorem exists_paperHalfPeriodRealization {k : ℕ} [h : Fact (2 ≤ k)] :
    Nonempty (PaperHalfPeriodRealization k) := by
  obtain ⟨C, hC, hm, hsm, him, hcov⟩ := exists_smooth_periodicEW_covering (reflectionBasepoint k)
  obtain ⟨t, ht⟩ := exists_paper_positional_symmetries C hC
  obtain ⟨f, hf, hb⟩ := exists_halfPeriod_disk_bijection C hC
  exact ⟨{
    C := C
    hC := hC
    t := t
    connected := periodicEW_pathConnected (reflectionBasepoint k) C hC
    geometry := ⟨hm, hsm, him⟩
    covering := hcov
    diskMap := f
    projection_agrees := hf
    disk_bijective := hb
    symmetries := ht }⟩

end KsIndex.KarcherData
