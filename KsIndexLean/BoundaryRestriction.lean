module

public import KsIndexLean.DiskTraceCovariance
public import KsIndexLean.DiskTraceIndependence

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Restriction of the actual boundary L² class to an arc measure. -/
def boundaryRestrict (A : Set Circle₁) (f : Lp ℂ 2 circleMeasure) :
    Lp ℂ 2 (circleMeasure.restrict A) :=
  ((Lp.memLp f).mono_measure Measure.restrict_le_self).toLp f

lemma boundaryRestrict_coe_ae (A : Set Circle₁) (f : Lp ℂ 2 circleMeasure) :
    (boundaryRestrict A f : Circle₁ → ℂ) =ᵐ[circleMeasure.restrict A] f :=
  MemLp.coeFn_toLp _

lemma boundaryRestrict_add (A : Set Circle₁) (f g : Lp ℂ 2 circleMeasure) :
    boundaryRestrict A (f + g) = boundaryRestrict A f + boundaryRestrict A g := by
  apply Lp.ext
  have h := (Lp.coeFn_add f g).filter_mono (ae_mono (Measure.restrict_le_self (s := A)))
  filter_upwards [boundaryRestrict_coe_ae A (f + g), boundaryRestrict_coe_ae A f,
    boundaryRestrict_coe_ae A g, h, Lp.coeFn_add (boundaryRestrict A f) (boundaryRestrict A g)]
    with w hs hf hg ha hb
  simp only [Pi.add_apply] at ha hb
  rw [hs, hb, hf, hg, ha]

lemma boundaryRestrict_smul (A : Set Circle₁) (c : ℂ) (f : Lp ℂ 2 circleMeasure) :
    boundaryRestrict A (c • f) = c • boundaryRestrict A f := by
  apply Lp.ext
  have h := (Lp.coeFn_smul c f).filter_mono (ae_mono (Measure.restrict_le_self (s := A)))
  filter_upwards [boundaryRestrict_coe_ae A (c • f), boundaryRestrict_coe_ae A f,
    h, Lp.coeFn_smul c (boundaryRestrict A f)] with w hs hf ha hb
  simp only [Pi.smul_apply] at ha hb
  rw [hs, hb, hf, ha]

lemma boundaryRestrict_norm_le (A : Set Circle₁) (f : Lp ℂ 2 circleMeasure) :
    ‖boundaryRestrict A f‖ ≤ ‖f‖ := by
  rw [boundaryRestrict, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_mono_measure f Measure.restrict_le_self)

def boundaryRestrictCLM (A : Set Circle₁) :
    Lp ℂ 2 circleMeasure →L[ℂ] Lp ℂ 2 (circleMeasure.restrict A) :=
  LinearMap.mkContinuous
    { toFun := boundaryRestrict A
      map_add' := boundaryRestrict_add A
      map_smul' := boundaryRestrict_smul A }
    1 (fun f => by simpa using boundaryRestrict_norm_le A f)

def arcTrace (A : Set Circle₁) : ComplexH1 →L[ℂ] Lp ℂ 2 (circleMeasure.restrict A) :=
  (boundaryRestrictCLM A).comp diskTraceCLM

/-- Zero Dirichlet trace on A; no normal-derivative constraint is added elsewhere. -/
def zeroTraceDomain (A : Set Circle₁) : Submodule ℂ ComplexH1 :=
  LinearMap.ker (arcTrace A).toLinearMap

lemma isClosed_zeroTraceDomain (A : Set Circle₁) : IsClosed (zeroTraceDomain A : Set ComplexH1) :=
  (arcTrace A).isClosed_ker

lemma mem_zeroTraceDomain (A : Set Circle₁) (u : ComplexH1) :
    u ∈ zeroTraceDomain A ↔
      (diskTraceCLM u : Circle₁ → ℂ) =ᵐ[circleMeasure.restrict A] 0 := by
  change boundaryRestrict A (diskTraceCLM u) = 0 ↔ _
  constructor
  · intro h
    have he := boundaryRestrict_coe_ae A (diskTraceCLM u)
    rw [h] at he
    exact he.symm.trans (Lp.coeFn_zero ℂ 2 (circleMeasure.restrict A))
  · intro h
    apply Lp.ext
    exact ((boundaryRestrict_coe_ae A (diskTraceCLM u)).trans h).trans
      (Lp.coeFn_zero ℂ 2 (circleMeasure.restrict A)).symm

lemma zeroTraceDomain_antitone {A B : Set Circle₁} (hAB : A ⊆ B) :
    zeroTraceDomain B ≤ zeroTraceDomain A := by
  intro u hu
  rw [mem_zeroTraceDomain] at hu ⊢
  exact hu.filter_mono (ae_mono (Measure.restrict_mono hAB le_rfl))

end KsIndex.Trace
