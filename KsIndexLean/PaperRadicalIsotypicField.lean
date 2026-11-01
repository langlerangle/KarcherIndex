module

public import KsIndexLean.BoundedJacobiCharacterExtension
public import KsIndexLean.FiberEmbed
public import KsIndexLean.PaperSmoothChainSector

@[expose] public section


/-! The actual weak paper radical produces fields in the original bounded
Jacobi isotypic fiber, with both weak disk components recovered. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.PaperSlitTransport
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Surface KsIndex.SurfaceForm
open KsIndex.SurfaceSym KsIndex.NullityDecomp KsIndex.PaperSlitAdapter

/-- Both symmetry identities hold on the entire normalized chain. -/
theorem rational_pair_radical_global_field {n j m : ℕ} [NeZero m]
    (u : paperSlitCharacterDomain ((n : ℝ) / m) j) (hrad : ∀ w, Bpair u w = 0) :
    ∃ U : ZMod (2 * m) → ℂ → ℂ,
      U ∈ BoundedJacobi 3 m ∧
      (∀ a z, U a (planeRotation (-(2 * Real.pi) / 3) z) = FormIndex.zeta 3 ^ j * U a z) ∧
      (∀ a z, U (a + 2) z = FormIndex.zeta m ^ n * U a z) ∧
      valueCLM u.val.1 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] U 1 ∧
      valueCLM u.val.2 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] U 0 := by
  obtain ⟨U, hE, hJ, hB, hR, hS, h1, h0⟩ := rational_pair_radical_bounded_field u hrad
  have hU : U ∈ BoundedJacobi 3 m := ⟨hE.1, hB, hJ, hE.2.2.2.1, hE.2.2.2.2⟩
  refine ⟨U, hU, boundedJacobi_paper_character_of_disk hU hR, ?_, h1, h0⟩
  simpa only [Spectral.paperRationalPhase_eq_zeta] using hS

/-- The weak radical is realized in the actual isotypic fiber used by the
surface-nullity decomposition, rather than a surrogate character carrier. -/
theorem rational_pair_radical_isotypic_field {n j m : ℕ} [NeZero m]
    (u : paperSlitCharacterDomain ((n : ℝ) / m) j) (hrad : ∀ w, Bpair u w = 0) :
    ∃ W : isotypicFiber 3 m j n,
      valueCLM u.val.1 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] (fun z => W.val (1, z)) ∧
      valueCLM u.val.2 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] (fun z => W.val (0, z)) := by
  obtain ⟨U, hU, hR, hS, h1, h0⟩ := rational_pair_radical_global_field u hrad
  have hB : (uncurryE m) U ∈ BoundedJacobiE 3 m :=
    mem_boundedJacobiE.mpr (by simpa only [LinearEquiv.symm_apply_apply] using hU)
  have hrot : (uncurryE m) U ∈ Module.End.eigenspace
      (rotE m ((rotUnit 3 : Circle) : ℂ)) (FormIndex.zeta 3 ^ j) := by
    apply Module.End.mem_eigenspace_iff.mpr
    funext a
    change U a.1 (((rotUnit 3 : Circle) : ℂ) * a.2) = FormIndex.zeta 3 ^ j * U a.1 a.2
    simpa only [rotUnit, Circle.coe_exp, planeRotation_apply, Nat.cast_ofNat] using hR a.1 a.2
  have hshift : (uncurryE m) U ∈ Module.End.eigenspace
      (shiftE m) (FormIndex.zeta m ^ n) := by
    apply Module.End.mem_eigenspace_iff.mpr
    funext a
    exact hS a.1 a.2
  have hmem : (uncurryE m) U ∈ isotypicFiber 3 m j n :=
    Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hB, hrot⟩, hshift⟩
  exact ⟨⟨(uncurryE m) U, hmem⟩, h1, h0⟩

end KsIndex.PaperSlitTransport
