module

public import KsIndexLean.AngularPairingAE
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

@[expose] public section


open Set MeasureTheory TopologicalSpace
open scoped ContDiff InnerProductSpace

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Continuity and a countable dense test family permit a single a.e. set. -/
lemma ae_forall_zero_of_continuous {X P : Type*} [MeasurableSpace X]
    {μ : Measure X} [TopologicalSpace P] [SeparableSpace P] {f : X → P → ℂ}
    (hc : ∀ x, Continuous (f x)) (ha : ∀ p, ∀ᵐ x ∂μ, f x p = 0) :
    ∀ᵐ x ∂μ, ∀ p, f x p = 0 := by
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense P
  have hD : ∀ᵐ x ∂μ, ∀ p ∈ D, f x p = 0 :=
    (ae_ball_iff hDc).mpr (fun p _ => ha p)
  filter_upwards [hD] with x hx
  intro p
  exact hDd.induction hx (isClosed_eq (hc x) continuous_const) p

def angularTestLp (H : ℂ → ℝ) (hH : Continuous H) : Lp ℂ 2 circleMeasure :=
  ContinuousMap.toLp 2 circleMeasure ℂ (realAngularMap H hH)

/-- The topology is inherited from L²×L², including both a test and its derivative. -/
def smoothAngularPairs : Set (Lp ℂ 2 circleMeasure × Lp ℂ 2 circleMeasure) :=
  {p | ∃ (H : ℂ → ℝ) (hH : ContDiff ℝ (⊤ : ℕ∞) H),
    p = (angularTestLp H hH.continuous,
      angularTestLp (angularTestDeriv H) (contDiff_angularTestDeriv hH).continuous)}

/-- The weak angular graph defined by all smooth ambient circle tests. -/
def circleAngularGraph : Submodule ℂ (Lp ℂ 2 circleMeasure × Lp ℂ 2 circleMeasure) where
  carrier := {v | ∀ p : smoothAngularPairs,
    inner ℂ p.val.2 v.1 + inner ℂ p.val.1 v.2 = 0}
  zero_mem' := by intro p; simp
  add_mem' := by
    intro v w hv hw p
    change inner ℂ p.val.2 (v.1 + w.1) + inner ℂ p.val.1 (v.2 + w.2) = 0
    simp only [inner_add_right]
    linear_combination hv p + hw p
  smul_mem' := by
    intro c v hv p
    change inner ℂ p.val.2 (c • v.1) + inner ℂ p.val.1 (c • v.2) = 0
    rw [inner_smul_right, inner_smul_right, ← mul_add, hv p, mul_zero]

lemma isClosed_circleAngularGraph :
    IsClosed (circleAngularGraph : Set (Lp ℂ 2 circleMeasure × Lp ℂ 2 circleMeasure)) := by
  change IsClosed {v : Lp ℂ 2 circleMeasure × Lp ℂ 2 circleMeasure |
    ∀ p : smoothAngularPairs,
    inner ℂ p.val.2 v.1 + inner ℂ p.val.1 v.2 = 0}
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro p
  exact isClosed_eq ((continuous_const.inner continuous_fst).add
    (continuous_const.inner continuous_snd)) continuous_const

lemma mem_circleAngularGraph_iff (F G : Lp ℂ 2 circleMeasure) :
    (F, G) ∈ circleAngularGraph ↔ ∀ (H : ℂ → ℝ) (hH : ContDiff ℝ (⊤ : ℕ∞) H),
      inner ℂ (angularTestLp (angularTestDeriv H) (contDiff_angularTestDeriv hH).continuous) F =
        -inner ℂ (angularTestLp H hH.continuous) G := by
  constructor
  · intro hv H hH
    exact add_eq_zero_iff_eq_neg.mp (hv ⟨_, H, hH, rfl⟩)
  · intro hv p
    obtain ⟨H, hH, hp⟩ := p.property
    change inner ℂ p.val.2 F + inner ℂ p.val.1 G = 0
    rw [hp]
    exact add_eq_zero_iff_eq_neg.mpr (hv H hH)

/-- One a.e. set now works simultaneously for every smooth angular test. -/
theorem disk_circleAngularGraph_ae (u : ComplexH1) :
    ∀ᵐ t ∂volume.restrict (Ioo (1 / 2 : ℝ) 1),
      (diskProfile u t, diskAngularProfile u t) ∈ circleAngularGraph := by
  change ∀ᵐ t ∂volume.restrict (Ioo (1 / 2 : ℝ) 1), ∀ p : smoothAngularPairs,
    inner ℂ p.val.2 (diskProfile u t) + inner ℂ p.val.1 (diskAngularProfile u t) = 0
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have : SecondCountableTopology (Lp ℂ 2 circleMeasure) := inferInstance
  apply ae_forall_zero_of_continuous
  · intro t
    exact ((continuous_snd.comp continuous_subtype_val).inner continuous_const).add
      ((continuous_fst.comp continuous_subtype_val).inner continuous_const)
  · intro p
    obtain ⟨H, hH, hp⟩ := p.property
    filter_upwards [disk_angular_profile_pairing_ae u hH] with t ht
    rw [hp]
    exact add_eq_zero_iff_eq_neg.mpr ht

lemma circleAngularGraph_unique {F G G' : Lp ℂ 2 circleMeasure}
    (hG : (F, G) ∈ circleAngularGraph) (hG' : (F, G') ∈ circleAngularGraph) : G = G' := by
  apply sub_eq_zero.mp
  apply realAngular_tests_separate
  intro H hH
  have h := (mem_circleAngularGraph_iff F G).mp hG H hH
  have h' := (mem_circleAngularGraph_iff F G').mp hG' H hH
  rw [inner_sub_right]
  exact sub_eq_zero.mpr (neg_injective (h.symm.trans h'))

end KsIndex.Trace
