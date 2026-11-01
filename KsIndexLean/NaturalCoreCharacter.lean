module

public import KsIndexLean.NaturalCoreTrace

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.SingleDisk

/-- An interior rotation equation passes to the genuine weak class. -/
lemma weakCharacter_of_value_eq (u : ComplexH1) {f : ℂ → ℂ} (θ : ℝ) (c : ℂ)
    (hu : (valueCLM u : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] f)
    (hf : ∀ z, f (planeRotation θ z) = c * f z) : u ∈ weakCharacterDomain θ c := by
  apply (mem_weakCharacterDomain θ c u).mpr
  apply valueCLM_injective
  rw [map_smul]
  apply Lp.ext
  have hr := (measurePreserving_planeRotation_disk θ).quasiMeasurePreserving.ae_eq_comp hu
  filter_upwards [diskRotation_value_ae θ u, hr, hu, Lp.coeFn_smul c (valueCLM u)]
    with z hrot hrz huz hcz
  rw [hrot, hcz]
  change valueCLM u (planeRotation θ z) = c * valueCLM u z
  change valueCLM u (planeRotation θ z) = f (planeRotation θ z) at hrz
  rw [hrz, huz, hf]

lemma naturalCoreH1_mem_character {k : ℕ} (hk : 1 ≤ k) {b1 b0 : Bool}
    (f : NatCc k b1 b0) (r : ℕ) (hf : f.val ∈ Erot1 k r) :
    naturalCoreH1 hk f ∈ mixedCharacterDomain k r b1 b0 := by
  refine ⟨naturalCoreH1_mem_mixed hk f, ?_⟩
  apply weakCharacter_of_value_eq _ _ _ (naturalCoreH1_value_ae hk f)
  intro z
  have he := congrFun (Module.End.mem_eigenspace_iff.mp hf) z
  simpa only [KsIndex.SingleDiskBridge.rot1_apply, Pi.smul_apply, smul_eq_mul,
    KsIndex.SurfaceSym.rotUnit, Circle.coe_exp, planeRotation_apply] using he

/-- The natural core in a paper rotation sector maps into the same weak sector. -/
def naturalCharacterToMixed {k : ℕ} (hk : 1 ≤ k) (r : ℕ) (b1 b0 : Bool) :
    ↥(NatCc k b1 b0 ⊓ Erot1 k r) →ₗ[ℂ] mixedCharacterDomain k r b1 b0 where
  toFun f := ⟨naturalCoreH1 hk ⟨f.val, f.property.1⟩,
    naturalCoreH1_mem_character hk ⟨f.val, f.property.1⟩ r f.property.2⟩
  map_add' f g := Subtype.ext (naturalCoreH1_add hk
    ⟨f.val, f.property.1⟩ ⟨g.val, g.property.1⟩)
  map_smul' c f := Subtype.ext (naturalCoreH1_smul hk c ⟨f.val, f.property.1⟩)

end KsIndex.Trace
