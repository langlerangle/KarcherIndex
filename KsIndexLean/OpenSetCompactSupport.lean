module

public import KsIndexLean.SingleDiskNat

@[expose] public section


/-! Compact support in a relatively compact open subset of the plane can be
expressed by uniform vanishing near its complement after extension by zero. -/
noncomputable section
open Set Topology
namespace KsIndex
attribute [local instance] Classical.propDecidable

/-- The canonical zero extension of a function on a subset. -/
def zeroExtendSet (Ω : Set ℂ) (f : Ω → ℂ) (z : ℂ) : ℂ :=
  if hz : z ∈ Ω then f ⟨z,hz⟩ else 0

lemma hasCompactSupport_iff_zeroExtendSet {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hcompact : IsCompact (closure Ω)) (f : Ω → ℂ) :
    HasCompactSupport f ↔ SingleDisk.SuppAwaySet Ωᶜ (zeroExtendSet Ω f) := by
  constructor
  · intro hf
    have hc := hf.image continuous_subtype_val
    have hd : Disjoint (Subtype.val '' tsupport f) Ωᶜ := by
      apply Set.disjoint_left.mpr
      rintro z ⟨q,hq,rfl⟩ hz
      exact hz q.property
    obtain ⟨ε,hε,he⟩ := Metric.exists_pos_forall_lt_edist hc hΩ.isClosed_compl hd
    refine ⟨ε,hε,fun z hz => ?_⟩
    classical
    unfold zeroExtendSet
    split_ifs with hzΩ
    · by_contra hn
      have ht : (⟨z,hzΩ⟩ : Ω) ∈ tsupport f := subset_tsupport f hn
      obtain ⟨p,hp,hzp⟩ := hz
      have hh := he z ⟨⟨z,hzΩ⟩,ht,rfl⟩ p hp
      have hdist : ε < ‖z-p‖ := by
        simpa only [edist_nndist, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe,
          coe_nndist, dist_eq_norm] using hh
      exact (not_lt_of_ge hdist.le) hzp
    · rfl
  · rintro ⟨ε,hε,hf⟩
    let K : Set ℂ := closure Ω ∩ {z | ∀ p ∈ Ωᶜ, ε ≤ ‖z-p‖}
    have hclosed : IsClosed K := by
      apply isClosed_closure.inter
      simp only [Set.ofPred_forall]
      apply isClosed_iInter
      intro p
      apply isClosed_iInter
      intro hp
      exact isClosed_le continuous_const ((continuous_id.sub continuous_const).norm)
    have hc : IsCompact K := hcompact.of_isClosed_subset hclosed (fun _ hz => hz.1)
    have hsub : K ⊆ Ω := by
      intro z hz
      by_contra hn
      have hh := hz.2 z hn
      simp only [sub_self,norm_zero] at hh
      exact (not_le_of_gt hε) hh
    have hc' : IsCompact ((Subtype.val : Ω → ℂ) ⁻¹' K) := by
      apply IsEmbedding.subtypeVal.isCompact_iff.mpr
      have he : (Subtype.val : Ω → ℂ) '' (Subtype.val ⁻¹' K) = K := by
        ext z
        constructor
        · rintro ⟨w,hw,rfl⟩
          exact hw
        · intro hz
          exact ⟨⟨z,hsub hz⟩,hz,rfl⟩
      rwa [he]
    apply HasCompactSupport.intro' hc' (hclosed.preimage continuous_subtype_val)
    intro q hq
    have hn : ¬ ∀ p ∈ Ωᶜ, ε ≤ ‖q.val-p‖ := by
      intro hh
      exact hq ⟨subset_closure q.property,hh⟩
    push Not at hn
    have hh := hf q.val hn
    simpa [zeroExtendSet,q.property] using hh

lemma tsupport_zeroExtendSet_subset {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hcompact : IsCompact (closure Ω)) {f : Ω → ℂ} (hf : HasCompactSupport f) :
    tsupport (zeroExtendSet Ω f) ⊆ Ω := by
  obtain ⟨ε,hε,hvan⟩ := (hasCompactSupport_iff_zeroExtendSet hΩ hcompact f).mp hf
  intro z hz
  by_contra hn
  have he : zeroExtendSet Ω f =ᶠ[𝓝 z] 0 := by
    filter_upwards [Metric.ball_mem_nhds z hε] with w hw
    exact hvan w ⟨z,hn,by simpa only [Metric.mem_ball,dist_eq_norm] using hw⟩
  exact (notMem_tsupport_iff_eventuallyEq.mpr he) hz

lemma hasCompactSupport_restrict_of_tsupport_subset {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : HasCompactSupport f) (hs : tsupport f ⊆ Ω) :
    HasCompactSupport (fun q : Ω => f q.val) := by
  have hc : IsCompact ((Subtype.val : Ω → ℂ) ⁻¹' tsupport f) := by
    apply IsEmbedding.subtypeVal.isCompact_iff.mpr
    have he : (Subtype.val : Ω → ℂ) '' (Subtype.val ⁻¹' tsupport f) = tsupport f := by
      ext z
      constructor
      · rintro ⟨w,hw,rfl⟩
        exact hw
      · intro hz
        exact ⟨⟨z,hs hz⟩,hz,rfl⟩
    rwa [he]
  apply HasCompactSupport.intro' hc ((isClosed_tsupport f).preimage continuous_subtype_val)
  intro q hq
  exact image_eq_zero_of_notMem_tsupport hq

end KsIndex
