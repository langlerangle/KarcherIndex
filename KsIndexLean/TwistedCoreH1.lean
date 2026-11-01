module

public import KsIndexLean.NaturalCoreForm

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.SingleDisk KsIndex.Twisted

lemma twistedCopy_mem_natural {k : ℕ} {ζ : ℂ} (hζ : ζ ≠ 0) (v : TwistedCc k ζ)
    (n : ZMod (2 * 1)) : v.val n ∈ NatCc k true true := by
  have hn := KsIndex.Bracket.TwistedCc_le_NCc hζ v.property
  have hr := KsIndex.Bracket.regular_of_mem_NCc hn
  refine ⟨hr.1 n, ?_, ?_, hn.1.2.2.2 n, ?_⟩
  · exact fun w hw => hr.2 n w hw.1.le
  · exact fun w hw => hr.2 n w hw.1.le
  · obtain ⟨ε, hε, hv⟩ := v.property.2
    exact ⟨ε, hε, hv n⟩

def twistedCopyNatural {k : ℕ} {ζ : ℂ} (hζ : ζ ≠ 0) (v : TwistedCc k ζ)
    (n : ZMod (2 * 1)) : NatCc k true true := ⟨v.val n, twistedCopy_mem_natural hζ v n⟩

/-- The H¹ carrier of one copy of a smooth twisted pair with nonzero phase.
The construction uses the copy's natural-core representative; the following
lemmas identify its value and weak derivatives almost everywhere. -/
def twistedCcCoreH1 {k : ℕ} (hk : 1 ≤ k) {ζ : ℂ} (hζ : ζ ≠ 0) (v : TwistedCc k ζ)
    (n : ZMod (2 * 1)) : ComplexH1 := naturalCoreH1 hk (twistedCopyNatural hζ v n)

lemma twistedCcCoreH1_value_ae {k : ℕ} (hk : 1 ≤ k) {ζ : ℂ} (hζ : ζ ≠ 0)
    (v : TwistedCc k ζ) (n : ZMod (2 * 1)) :
    (valueCLM (twistedCcCoreH1 hk hζ v n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] v.val n :=
  naturalCoreH1_value_ae hk (twistedCopyNatural hζ v n)

lemma twistedCcCoreH1_dx_ae {k : ℕ} (hk : 1 ≤ k) {ζ : ℂ} (hζ : ζ ≠ 0)
    (v : TwistedCc k ζ) (n : ZMod (2 * 1)) :
    (dxCLM (twistedCcCoreH1 hk hζ v n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
      (fun z => fderiv ℝ (v.val n) z 1) :=
  naturalCoreH1_dx_ae hk (twistedCopyNatural hζ v n)

lemma twistedCcCoreH1_dy_ae {k : ℕ} (hk : 1 ≤ k) {ζ : ℂ} (hζ : ζ ≠ 0)
    (v : TwistedCc k ζ) (n : ZMod (2 * 1)) :
    (dyCLM (twistedCcCoreH1 hk hζ v n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
      (fun z => fderiv ℝ (v.val n) z Complex.I) :=
  naturalCoreH1_dy_ae hk (twistedCopyNatural hζ v n)

lemma twistedCcCoreH1_add {k : ℕ} (hk : 1 ≤ k) {ζ : ℂ} (hζ : ζ ≠ 0)
    (v w : TwistedCc k ζ) (n : ZMod (2 * 1)) :
    twistedCcCoreH1 hk hζ (v + w) n = twistedCcCoreH1 hk hζ v n + twistedCcCoreH1 hk hζ w n :=
  naturalCoreH1_add hk (twistedCopyNatural hζ v n) (twistedCopyNatural hζ w n)

lemma twistedCcCoreH1_smul {k : ℕ} (hk : 1 ≤ k) {ζ : ℂ} (hζ : ζ ≠ 0)
    (c : ℂ) (v : TwistedCc k ζ) (n : ZMod (2 * 1)) :
    twistedCcCoreH1 hk hζ (c • v) n = c • twistedCcCoreH1 hk hζ v n :=
  naturalCoreH1_smul hk c (twistedCopyNatural hζ v n)

end KsIndex.Trace
