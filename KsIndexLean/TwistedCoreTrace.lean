module

public import KsIndexLean.TwistedCoreH1
public import KsIndexLean.PhaseGermTrace
public import KsIndexLean.WeakTransmissionDomains

@[expose] public section


open Set MeasureTheory
open scoped ContDiff

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Twisted

lemma twistedCcCoreH1_arc1 {k : ℕ} (hk : 1 ≤ k) {ζ : ℂ} (hζ : ζ ≠ 0)
    (v : TwistedCc k ζ) :
    arcTrace (boundaryArc k 1) (twistedCcCoreH1 hk hζ v 0) =
      arcTrace (boundaryArc k 1) (twistedCcCoreH1 hk hζ v 1) := by
  have he : phaseGerm 1 (v.val 0) (v.val 1) = Surface.glue v.val 0 := by
    funext z
    simp only [phaseGerm, Surface.glue, one_mul, zero_add, KsIndex.Bracket.σ_apply]
  have ht := arcTrace_phaseGerm (A := boundaryArc k 1) _ _ 1
    (twistedCcCoreH1_value_ae hk hζ v 0) (twistedCcCoreH1_value_ae hk hζ v 1)
    (fun w hw => by
      rw [he]
      exact v.property.1.2.1 w (by rwa [seamArc_one_zero]))
  simpa only [one_smul] using ht

lemma twistedCcCoreH1_arc0 {k : ℕ} (hk : 1 ≤ k) {ζ : ℂ} (hζ : ζ ≠ 0)
    (v : TwistedCc k ζ) :
    arcTrace (boundaryArc k 0) (twistedCcCoreH1 hk hζ v 1) =
      ζ • arcTrace (boundaryArc k 0) (twistedCcCoreH1 hk hζ v 0) := by
  have he : phaseGerm ζ (v.val 1) (v.val 0) = glueTw ζ v.val := by
    funext z
    rfl
  apply arcTrace_phaseGerm _ _ ζ
    (twistedCcCoreH1_value_ae hk hζ v 1) (twistedCcCoreH1_value_ae hk hζ v 0)
  intro w hw
  rw [he]
  exact v.property.1.2.2.1 w (by rwa [seamArc_one_one])

/-- The ordered weak pair is (copy 1, copy 0), preserving the twist phase. -/
def twistedCoreToSlit {k : ℕ} (hk : 1 ≤ k) {ζ : ℂ} (hζ : ζ ≠ 0) :
    TwistedCc k ζ →ₗ[ℂ] slitTraceDomain k ζ where
  toFun v := ⟨(twistedCcCoreH1 hk hζ v 1, twistedCcCoreH1 hk hζ v 0),
    (mem_slitTraceDomain k ζ _).mpr
      ⟨(twistedCcCoreH1_arc1 hk hζ v).symm, twistedCcCoreH1_arc0 hk hζ v⟩⟩
  map_add' v w := Subtype.ext (Prod.ext (twistedCcCoreH1_add hk hζ v w 1)
    (twistedCcCoreH1_add hk hζ v w 0))
  map_smul' c v := Subtype.ext (Prod.ext (twistedCcCoreH1_smul hk hζ c v 1)
    (twistedCcCoreH1_smul hk hζ c v 0))

/-- The paper phase is nonzero and uses exactly the same ordered trace equation. -/
def twistedCoreToPaperSlit (α : ℝ) :
    TwistedCc 3 (Complex.exp ((2 * Real.pi * α) * Complex.I)) →ₗ[ℂ] paperSlitDomain α :=
  twistedCoreToSlit (by norm_num) (Complex.exp_ne_zero _)

lemma twistedCoreToSlit_character {k : ℕ} (hk : 1 ≤ k) {ζ : ℂ} (hζ : ζ ≠ 0)
    (v : TwistedCc k ζ) (r : ℕ)
    (hr : ∀ n, v.val n ∈ KsIndex.SingleDisk.Erot1 k r) :
    (twistedCoreToSlit hk hζ v).val ∈
      pairCharacterDomain (-(2 * Real.pi) / k) (KsIndex.FormIndex.zeta k ^ r) :=
  ⟨(naturalCoreH1_mem_character hk (twistedCopyNatural hζ v 1) r (hr 1)).2,
    (naturalCoreH1_mem_character hk (twistedCopyNatural hζ v 0) r (hr 0)).2⟩

end KsIndex.Trace
