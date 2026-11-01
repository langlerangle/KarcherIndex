module

public import KsIndexLean.MixedFourCopyJacobi
public import KsIndexLean.GammaEndProducerGeneralK
public import KsIndexLean.MixedHalfDiskFiniteEnergy

@[expose] public section


/-! Bounded classical representatives of the mixed weak radical. Boundedness
comes from the four-copy continuation and the finite-gradient-energy theorem. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace KsIndex.Trace
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.WeakH1 KsIndex.FormIndex

lemma dnFourCopy_bound_restrict (k : ℕ) (H : ℂ → ℂ)
    (hb : IsBounded (m := 2) (dnFourCopy k H)) :
    ∃ C : ℝ, ∀ w : ℂ, ‖w‖ ≤ 1 → w ∉ punctures k → ‖H w‖ ≤ C := by
  obtain ⟨C, hC⟩ := hb
  refine ⟨C, fun w hw hp => ?_⟩
  have hh : ‖w‖ ≤ 1 ∧ w ∉ punctures k := ⟨hw, hp⟩
  simpa only [dnFourCopy, ite_eq_left hh, dnCopySign_zero, one_mul] using hC 0 w

/-- Every element of the paper's DN character radical has a bounded classical
half-disk representative with the actual Dirichlet and Neumann conditions. -/
theorem dn_radical_classical_representative {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (u : ComplexH1) (hu : u ∈ mixedCharacterDomain k j true false)
    (hQ : ∀ v ∈ mixedCharacterDomain k j true false,
      weakJacobi (surfacePotential k) u v = 0) :
    ∃ U : ClassicalMixedHalfDiskJacobi k true false,
      valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] U.value := by
  obtain ⟨f, hf, ha, he⟩ := Weq.mixedCharacter_radical_classical hk j true false
    ⟨u, hu⟩ (fun v => hQ v v.property)
  obtain ⟨F0, h0, ha0, _, hz0⟩ := dn_radical_dirichlet_arc_classical hk j u hu hQ
  obtain ⟨F1, h1, ha1, _, hn1⟩ := dn_radical_neumann_arc_classical hk j u hu hQ
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
  have hG : dnFourCopy k H ∈ FaithfulInjection.GradEnergySmooth k 2 :=
    ⟨dnFourCopy_patch_isSmooth (by omega) f F0 F1 hf h0 h1 hi0 hi1 ho0 ho1,
      dnFourCopy_energy (by omega) H hH.1 hE, dnFourCopy_punctureZero k H,
      dnFourCopy_patch_seamVal k f F0 F1 hi0 hz0⟩
  have hb := GammaProducer.bounded_of_jacobi_gradEnergySmooth hk hG
    (dnFourCopy_isJacobiField hk H hH.1 hH.2)
  refine ⟨⟨H, hH.1, dnFourCopy_bound_restrict k H hb, hH.2, ?_⟩,
    mixedDiskPatch_value_ae k u f F0 F1 ha⟩
  intro w hw hp
  rcases mem_arc_of_not_puncture hw hp with hw0 | hw1
  · refine ⟨F0, h0.contDiffAt ((seamDomain _ _).isOpen.mem_nhds
      (arc_mem_seamDomain hw0)), ?_, ?_, fun _ => hz0 w hw0⟩
    · filter_upwards [mixedDiskPatch_dirichlet_germ k f F0 F1 hi0 hw0] with z hz
      exact fun _ => hz
    · intro hw1
      have ha0 : (w ^ k).re < 0 := by simpa [arc] using hw0.2
      have ha1 : 0 < (w ^ k).re := by simpa [arc] using hw1.2
      linarith
  · refine ⟨F1, h1.contDiffAt ((seamDomain _ _).isOpen.mem_nhds
      (arc_mem_seamDomain hw1)), ?_, fun _ => hn1 w hw1, ?_⟩
    · filter_upwards [mixedDiskPatch_neumann_germ k f F0 F1 hi1 hw1] with z hz
      exact fun _ => hz
    · intro hw0
      have ha0 : (w ^ k).re < 0 := by simpa [arc] using hw0.2
      have ha1 : 0 < (w ^ k).re := by simpa [arc] using hw1.2
      linarith

/-- Converting the bounded classical representative back to H¹ recovers
exactly the original weak element, not merely its values on a test family. -/
theorem dn_radical_toH1_surjective {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (u : ComplexH1) (hu : u ∈ mixedCharacterDomain k j true false)
    (hQ : ∀ v ∈ mixedCharacterDomain k j true false,
      weakJacobi (surfacePotential k) u v = 0) :
    ∃ U : ClassicalMixedHalfDiskJacobi k true false, U.toH1 hk = u := by
  obtain ⟨U, ha⟩ := dn_radical_classical_representative hk j u hu hQ
  refine ⟨U, valueCLM_injective ?_⟩
  exact Lp.ext ((U.toH1_value_ae hk).trans ha.symm)

end KsIndex.Trace
