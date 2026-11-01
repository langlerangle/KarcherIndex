module

public import KsIndexLean.WeakTransmissionDomains

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma circleRotate_boundaryArc_preimage (k j : ℕ) (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) :
    circleRotate θ ⁻¹' boundaryArc k j = boundaryArc k j := by
  ext w
  simp only [Set.mem_preimage, mem_boundaryArc]
  change (-1 : ℝ) ^ j * ((Complex.exp (θ * Complex.I) * (w : ℂ)) ^ k).re < 0 ↔ _
  rw [mul_pow, hθ, one_mul]

lemma measurePreserving_arcRotation (A : Set Circle₁) (hA : MeasurableSet A)
    (θ : ℝ) (hθ : circleRotate θ ⁻¹' A = A) :
    MeasurePreserving (circleRotate θ) (circleMeasure.restrict A) (circleMeasure.restrict A) := by
  simpa only [hθ] using (measurePreserving_circleRotate θ).restrict_preimage hA

def arcRotation (A : Set Circle₁) (hA : MeasurableSet A)
    (θ : ℝ) (hθ : circleRotate θ ⁻¹' A = A) :
    Lp ℂ 2 (circleMeasure.restrict A) →ₗᵢ[ℂ] Lp ℂ 2 (circleMeasure.restrict A) :=
  Lp.compMeasurePreservingₗᵢ ℂ (circleRotate θ) (measurePreserving_arcRotation A hA θ hθ)

lemma boundaryRestrict_rotation (A : Set Circle₁) (hA : MeasurableSet A)
    (θ : ℝ) (hθ : circleRotate θ ⁻¹' A = A) (f : Lp ℂ 2 circleMeasure) :
    boundaryRestrict A (boundaryRotation θ f) = arcRotation A hA θ hθ (boundaryRestrict A f) := by
  apply Lp.ext
  have hrot := (boundaryRotation_coe_ae θ f).filter_mono
    (ae_mono (Measure.restrict_le_self (s := A)))
  have hcomp := (measurePreserving_arcRotation A hA θ hθ).quasiMeasurePreserving.ae_eq_comp
    (boundaryRestrict_coe_ae A f)
  have harc := Lp.coeFn_compMeasurePreserving (boundaryRestrict A f)
    (measurePreserving_arcRotation A hA θ hθ)
  filter_upwards [boundaryRestrict_coe_ae A (boundaryRotation θ f), hrot, hcomp, harc]
    with w hr hb hc ha
  exact hr.trans (hb.trans (hc.symm.trans ha.symm))

lemma arcTrace_rotation (A : Set Circle₁) (hA : MeasurableSet A)
    (θ : ℝ) (hθ : circleRotate θ ⁻¹' A = A) (u : ComplexH1) :
    arcTrace A (diskRotation θ u) = arcRotation A hA θ hθ (arcTrace A u) := by
  change boundaryRestrict A (diskTraceCLM (diskRotation θ u)) = _
  rw [diskTrace_rotation]
  exact boundaryRestrict_rotation A hA θ hθ (diskTraceCLM u)

lemma arcTrace_rotation_phase (A : Set Circle₁) (hA : MeasurableSet A)
    (θ : ℝ) (hθ : circleRotate θ ⁻¹' A = A) (c : ℂ) (u v : ComplexH1)
    (h : arcTrace A u = c • arcTrace A v) :
    arcTrace A (diskRotation θ u) = c • arcTrace A (diskRotation θ v) := by
  rw [arcTrace_rotation A hA θ hθ u, arcTrace_rotation A hA θ hθ v, h, map_smul]

end KsIndex.Trace
