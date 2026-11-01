module

public import KsIndexLean.NaturalCoreH1
public import KsIndexLean.ArcLocalAgreement
public import KsIndexLean.WeakBoundaryDomains

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.SingleDisk

/-- Vanishing near a boundary set forces the actual weak trace to vanish there. -/
lemma trace_zero_of_suppAwaySet (u : ComplexH1) {f : ℂ → ℂ} {S : Set ℂ}
    (hf : SuppAwaySet S f)
    (he : (valueCLM u : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] f)
    {A : Set Circle₁} (hA : ∀ w ∈ A, (w : ℂ) ∈ S) :
    (diskTraceCLM u : Circle₁ → ℂ) =ᵐ[circleMeasure.restrict A] 0 := by
  obtain ⟨ε, hε, hf⟩ := hf
  apply diskTrace_local_agreement (f := fun _ => 0)
  intro w hw
  refine ⟨Metric.ball (w : ℂ) ε, Metric.isOpen_ball, Metric.mem_ball_self hε,
    continuousOn_const, ?_⟩
  filter_upwards [he] with z hz hzO
  rw [hz]
  exact hf z ⟨w, hA w hw, by simpa [dist_eq_norm] using Metric.mem_ball.mp hzO⟩

lemma naturalCoreH1_mem_mixed {k : ℕ} (hk : 1 ≤ k) {b1 b0 : Bool}
    (f : NatCc k b1 b0) : naturalCoreH1 hk f ∈ mixedTraceDomain k b1 b0 := by
  constructor
  · apply (mem_naturalArcDomain k 1 b1 _).mpr
    intro hb
    have hf := f.property.2.1
    simp only [hb, ArcCond] at hf
    exact trace_zero_of_suppAwaySet _ hf (naturalCoreH1_value_ae hk f)
      (fun _ hw => arc_one_subset_slitC hw)
  · apply (mem_naturalArcDomain k 0 b0 _).mpr
    intro hb
    have hf := f.property.2.2.1
    simp only [hb, ArcCond] at hf
    exact trace_zero_of_suppAwaySet _ hf (naturalCoreH1_value_ae hk f)
      (fun _ hw => KsIndex.Bracket.arc_zero_subset_slit hw)

lemma naturalCoreH1_add {k : ℕ} (hk : 1 ≤ k) {b1 b0 : Bool} (f g : NatCc k b1 b0) :
    naturalCoreH1 hk (f + g) = naturalCoreH1 hk f + naturalCoreH1 hk g := by
  apply valueCLM_injective
  rw [map_add]
  apply Lp.ext
  filter_upwards [naturalCoreH1_value_ae hk (f + g), naturalCoreH1_value_ae hk f,
    naturalCoreH1_value_ae hk g,
    Lp.coeFn_add (valueCLM (naturalCoreH1 hk f)) (valueCLM (naturalCoreH1 hk g))]
    with z hs hf hg ha
  rw [ha, Pi.add_apply, hs, hf, hg]
  rfl

lemma naturalCoreH1_smul {k : ℕ} (hk : 1 ≤ k) {b1 b0 : Bool} (c : ℂ) (f : NatCc k b1 b0) :
    naturalCoreH1 hk (c • f) = c • naturalCoreH1 hk f := by
  apply valueCLM_injective
  rw [map_smul]
  apply Lp.ext
  filter_upwards [naturalCoreH1_value_ae hk (c • f), naturalCoreH1_value_ae hk f,
    Lp.coeFn_smul c (valueCLM (naturalCoreH1 hk f))] with z hs hf hc
  rw [hc, Pi.smul_apply, hs, hf]
  rfl

/-- The existing natural test core maps into the genuine mixed weak form domain. -/
def naturalCoreToMixed {k : ℕ} (hk : 1 ≤ k) (b1 b0 : Bool) :
    NatCc k b1 b0 →ₗ[ℂ] mixedTraceDomain k b1 b0 where
  toFun f := ⟨naturalCoreH1 hk f, naturalCoreH1_mem_mixed hk f⟩
  map_add' f g := Subtype.ext (naturalCoreH1_add hk f g)
  map_smul' c f := Subtype.ext (naturalCoreH1_smul hk c f)

end KsIndex.Trace
