module

public import KsIndexLean.MixedFourCopySeams
public import KsIndexLean.GradEnergySmooth
public import KsIndexLean.GeneralRadicalRegularity

@[expose] public section


/-! The mixed weak radical continues to a smooth finite-gradient-energy
Jacobi field on the four-copy chain. Boundedness is not an input. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace KsIndex.Trace
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.WeakH1 KsIndex.FormIndex

lemma dnFourCopy_isJacobiField {k : ℕ} (hk : 2 ≤ k) (H : ℂ → ℂ)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H (Surface.disk : Set ℂ))
    (hP : ∀ z ∈ (Surface.disk : Set ℂ), laplacian H z + (potV k z : ℂ) * H z = 0) :
    IsJacobiField k 2 (dnFourCopy k H) := by
  intro n w hw
  have he : dnFourCopy k H n =ᶠ[nhds w] dnCopySign n • H :=
    Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hw)
      (dnFourCopy_inner (by omega) H n)
  have hd := hH.contDiffAt (Metric.isOpen_ball.mem_nhds hw)
  have hv : dnFourCopy k H n w = dnCopySign n * H w := he.self_of_nhds
  rw [laplacianG, JacobiFamily.laplacian_congr he, laplacian_smul (dnCopySign n) hd, hv]
  have hj := JacobiFields.laplacianG_add_absASq_of_flat hk hw (hP w hw)
  rw [laplacianG] at hj
  linear_combination dnCopySign n * hj

/-- Odd reflection on arc zero and even reflection on arc one produce an
actual four-copy Jacobi field with finite gradient energy and period-shift
anti-invariance, as used in the paper's mixed nullity argument. -/
theorem dn_radical_fourCopy {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (u : ComplexH1) (hu : u ∈ mixedCharacterDomain k j true false)
    (hQ : ∀ v ∈ mixedCharacterDomain k j true false,
      weakJacobi (surfacePotential k) u v = 0) :
    ∃ H : ℂ → ℂ,
      valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] H ∧
      dnFourCopy k H ∈ FaithfulInjection.GradEnergySmooth k 2 ∧
      IsJacobiField k 2 (dnFourCopy k H) ∧
      ∀ n z, dnFourCopy k H (n + 2) z = -dnFourCopy k H n z := by
  obtain ⟨f, hf, ha, he⟩ := Weq.mixedCharacter_radical_classical hk j true false
    ⟨u, hu⟩ (fun v => hQ v v.property)
  obtain ⟨F0, h0, ha0, _, hz0⟩ := dn_radical_dirichlet_arc_classical hk j u hu hQ
  obtain ⟨F1, h1, ha1, _, _⟩ := dn_radical_neumann_arc_classical hk j u hu hQ
  have hi0 := seam_representative_eq_inner (isOpen_boundaryArc k 0) u u (-1)
    h0.continuousOn hf.continuousOn ha0 ha
  have hi1 := seam_representative_eq_inner (isOpen_boundaryArc k 1) u u 1
    h1.continuousOn hf.continuousOn ha1 ha
  have ho0 := seam_representative_eq_outer (isOpen_boundaryArc k 0) u u (-1)
    h0.continuousOn hf.continuousOn ha0 ha
  have ho1 := seam_representative_eq_outer (isOpen_boundaryArc k 1) u u 1
    h1.continuousOn hf.continuousOn ha1 ha
  let H := mixedDiskPatch k f F0 F1
  have hH := mixedDiskPatch_interior k f F0 F1 hf he
  have hE := mixedDiskPatch_energy_integrable k u f F0 F1 hf ha he
  refine ⟨H, mixedDiskPatch_value_ae k u f F0 F1 ha, ?_,
    dnFourCopy_isJacobiField hk H hH.1 hH.2, dnFourCopy_antiperiodic k H⟩
  exact ⟨dnFourCopy_patch_isSmooth (by omega) f F0 F1 hf h0 h1 hi0 hi1 ho0 ho1,
    dnFourCopy_energy (by omega) H hH.1 hE, dnFourCopy_punctureZero k H,
    dnFourCopy_patch_seamVal k f F0 F1 hi0 hz0⟩

end KsIndex.Trace
