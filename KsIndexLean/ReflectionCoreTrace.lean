module

public import KsIndexLean.NaturalCoreForm
public import KsIndexLean.SmoothGermTrace

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.SingleDisk

/-- A reflection germ supplies a one-sided extension, for either reflection sign. -/
lemma singleCc_le_natural_neumann (k : ℕ) (b1 b0 : Bool) :
    SingleCc k b1 b0 ≤ NatCc k true b0 := by
  intro f hf
  refine ⟨hf.1, ?_, (arc0Cond_eq k b0 f).mp hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.2⟩
  intro w hw
  refine ⟨KsIndex.SingleDisk.refl (sgn b1) f, hf.2.1 w hw,
    Filter.Eventually.of_forall fun z hz => ?_⟩
  have hn : ‖z‖ ≤ 1 := (KsIndex.SurfaceForm.mem_disk_iff.mp hz).le
  simp only [KsIndex.SingleDisk.refl, ite_eq_left hn]

def reflectionAsNatural {k : ℕ} {b1 b0 : Bool} (f : SingleCc k b1 b0) : NatCc k true b0 :=
  ⟨f.val, singleCc_le_natural_neumann k b1 b0 f.property⟩

def reflectionCoreH1 {k : ℕ} (hk : 1 ≤ k) {b1 b0 : Bool} (f : SingleCc k b1 b0) : ComplexH1 :=
  naturalCoreH1 hk (reflectionAsNatural f)

lemma reflectionCoreH1_value_ae {k : ℕ} (hk : 1 ≤ k) {b1 b0 : Bool}
    (f : SingleCc k b1 b0) :
    (valueCLM (reflectionCoreH1 hk f) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] f.val :=
  naturalCoreH1_value_ae hk (reflectionAsNatural f)

/-- The trace is the boundary value of the actual smooth reflection germ. -/
lemma reflectionCoreH1_arc1_trace {k : ℕ} (hk : 1 ≤ k) {b1 b0 : Bool}
    (f : SingleCc k b1 b0) :
    (diskTraceCLM (reflectionCoreH1 hk f) : Circle₁ → ℂ)
      =ᵐ[circleMeasure.restrict (boundaryArc k 1)] (fun w => f.val (w : ℂ)) := by
  have he : (valueCLM (reflectionCoreH1 hk f) : ℂ → ℂ)
      =ᵐ[volume.restrict (disk : Set ℂ)] KsIndex.SingleDisk.refl (sgn b1) f.val := by
    filter_upwards [reflectionCoreH1_value_ae hk f,
      ae_restrict_mem disk.isOpen.measurableSet] with z hz hzD
    rw [hz, KsIndex.SingleDisk.refl,
      ite_eq_left (KsIndex.SurfaceForm.mem_disk_iff.mp hzD).le]
  have ht := diskTrace_smooth_germs (reflectionCoreH1 hk f)
    (A := boundaryArc k 1) (fun w hw => f.property.2.1 w hw) he
  filter_upwards [ht] with w hw
  simpa only [KsIndex.SingleDisk.refl, mem_sphere_zero_iff_norm.mp w.property,
    le_refl, ite_true] using hw

lemma reflectionCoreH1_mem_mixed {k : ℕ} (hk : 1 ≤ k) {b1 b0 : Bool}
    (f : SingleCc k b1 b0) : reflectionCoreH1 hk f ∈ mixedTraceDomain k b1 b0 := by
  refine ⟨?_, (naturalCoreH1_mem_mixed hk (reflectionAsNatural f)).2⟩
  apply (mem_naturalArcDomain k 1 b1 _).mpr
  intro hb
  filter_upwards [reflectionCoreH1_arc1_trace hk f] with w hw
  exact hw.trans (f.property.2.2.2.2.1 hb w (mem_sphere_zero_iff_norm.mp w.property))

/-- Both encodings enter the same mixed weak domain, without identifying their cores. -/
def reflectionCoreToMixed {k : ℕ} (hk : 1 ≤ k) (b1 b0 : Bool) :
    SingleCc k b1 b0 →ₗ[ℂ] mixedTraceDomain k b1 b0 where
  toFun f := ⟨reflectionCoreH1 hk f, reflectionCoreH1_mem_mixed hk f⟩
  map_add' f g := Subtype.ext (naturalCoreH1_add hk (reflectionAsNatural f) (reflectionAsNatural g))
  map_smul' c f := Subtype.ext (naturalCoreH1_smul hk c (reflectionAsNatural f))

lemma reflectionCoreToMixed_form {k : ℕ} (hk : 2 ≤ k) (b1 b0 : Bool)
    (f : SingleCc k b1 b0) :
    weakJacobi (surfacePotential k) (reflectionCoreToMixed (by omega) b1 b0 f).val
      (reflectionCoreToMixed (by omega) b1 b0 f).val =
      (KsIndex.SingleDiskBridge.Qd k f.val : ℂ) :=
  smooth_weakJacobi_self_eq_Qd hk (naturalCoreData (by omega) (reflectionAsNatural f))

lemma reflectionCoreH1_mem_character {k : ℕ} (hk : 1 ≤ k) {b1 b0 : Bool}
    (f : SingleCc k b1 b0) (r : ℕ) (hf : f.val ∈ Erot1 k r) :
    reflectionCoreH1 hk f ∈ mixedCharacterDomain k r b1 b0 :=
  ⟨reflectionCoreH1_mem_mixed hk f,
    (naturalCoreH1_mem_character hk (reflectionAsNatural f) r hf).2⟩

def reflectionCharacterToMixed {k : ℕ} (hk : 1 ≤ k) (r : ℕ) (b1 b0 : Bool) :
    ↥(SingleCc k b1 b0 ⊓ Erot1 k r) →ₗ[ℂ] mixedCharacterDomain k r b1 b0 where
  toFun f := ⟨reflectionCoreH1 hk ⟨f.val, f.property.1⟩,
    reflectionCoreH1_mem_character hk ⟨f.val, f.property.1⟩ r f.property.2⟩
  map_add' f g := Subtype.ext (naturalCoreH1_add hk
    (reflectionAsNatural ⟨f.val, f.property.1⟩) (reflectionAsNatural ⟨g.val, g.property.1⟩))
  map_smul' c f := Subtype.ext (naturalCoreH1_smul hk c (reflectionAsNatural ⟨f.val, f.property.1⟩))

end KsIndex.Trace
