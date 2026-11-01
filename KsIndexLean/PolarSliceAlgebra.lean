module

public import KsIndexLean.PolarPullbackContracts

@[expose] public section


open Set MeasureTheory

namespace KsIndex.Trace

lemma sliceLp_coe_ae {a b : ℝ} (ha : 0 < a) {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (annulusSet a b))) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      (sliceLp a b u t : Circle₁ → ℂ) =ᵐ[circleMeasure] sliceFun u t := by
  filter_upwards [ae_sliceFun_memLp ha hu, ae_restrict_mem measurableSet_Ioo] with t ht htI
  rw [sliceLp_of_memLp htI ht]
  exact ht.coeFn_toLp

lemma sliceLp_add_ae {a b : ℝ} (ha : 0 < a) {u v : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (annulusSet a b)))
    (hv : MemLp v 2 (volume.restrict (annulusSet a b))) :
    sliceLp a b (u + v) =ᵐ[volume.restrict (Ioo a b)] sliceLp a b u + sliceLp a b v := by
  filter_upwards [sliceLp_coe_ae ha hu, sliceLp_coe_ae ha hv,
    sliceLp_coe_ae ha (hu.add hv)] with t ht hu' hs
  apply Lp.ext
  filter_upwards [ht, hu', hs, Lp.coeFn_add (sliceLp a b u t) (sliceLp a b v t)]
    with w hw hvw hsw ha'
  change sliceLp a b (u + v) t w = (sliceLp a b u t + sliceLp a b v t) w
  rw [ha', Pi.add_apply, hw, hvw, hsw]
  rfl

lemma sliceLp_smul_ae {a b : ℝ} (ha : 0 < a) (c : ℂ) {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (annulusSet a b))) :
    sliceLp a b (c • u) =ᵐ[volume.restrict (Ioo a b)] c • sliceLp a b u := by
  filter_upwards [sliceLp_coe_ae ha hu, sliceLp_coe_ae ha (hu.const_smul c)] with t ht hs
  apply Lp.ext
  filter_upwards [ht, hs, Lp.coeFn_smul c (sliceLp a b u t)] with w hw hsw hc
  change sliceLp a b (c • u) t w = (c • sliceLp a b u t) w
  rw [hc, Pi.smul_apply, hw, hsw]
  rfl

end KsIndex.Trace
