module

public import KsIndexLean.PaperRadicalIsotypicField

@[expose] public section


/-! The constructed field is a preimage under `fiberToSphereRadical`.
Surjectivity and injectivity give a linear equivalence without a dimension hypothesis. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.PaperSlitTransport
open KsIndex.Trace KsIndex.WeakH1 KsIndex.NullityDecomp KsIndex.Spectral
open KsIndex.PaperSlitAdapter

lemma fiberToSlit_eq_of_values {m n j : ℕ} [NeZero m]
    (W : isotypicFiber 3 m j n) (u : paperSlitCharacterDomain ((n : ℝ) / m) j)
    (h1 : valueCLM u.val.1 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] (fun z => W.val (1, z)))
    (h0 : valueCLM u.val.2 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] (fun z => W.val (0, z))) :
    paperChainSlitEquiv m n j (fiberToSectorLin W) = u := by
  apply Subtype.ext
  rw [paperChainSlitEquiv_coordinates]
  change (chainChartCoordinatesCLM 3 m (fiberToChain W) 1,
    chainChartCoordinatesCLM 3 m (fiberToChain W) 0) = u.val
  rw [fiberToChain_coord]
  apply Prod.ext
  · apply valueCLM_injective
    apply Lp.ext
    exact (energySmoothCopy_value_ae (fiberES W) 1).trans h1.symm
  · apply valueCLM_injective
    apply Lp.ext
    exact (energySmoothCopy_value_ae (fiberES W) 0).trans h0.symm

/-- Surjectivity onto the actual paper slit radical, with the established
chain-to-slit coordinate map. -/
theorem pair_radical_has_fiber_preimage {m n j : ℕ} [NeZero m]
    (u : paperSlitCharacterDomain ((n : ℝ) / m) j) (hrad : ∀ w, Bpair u w = 0) :
    ∃ W : isotypicFiber 3 m j n, paperChainSlitEquiv m n j (fiberToSectorLin W) = u := by
  obtain ⟨W, h1, h0⟩ := rational_pair_radical_isotypic_field u hrad
  exact ⟨W, fiberToSlit_eq_of_values W u h1 h0⟩

/-- The map `fiberToSphereRadical` is surjective. -/
theorem fiberToSphereRadical_surjective {m n j : ℕ} [NeZero m] :
    Function.Surjective (fiberToSphereRadical (m := m) (r := j) (a := n)) := by
  intro q
  let e := paperSlitCharacterSphereEquiv ((n : ℝ) / m) j
  let u := e.symm q.val
  have hu : e u = q.val := e.apply_symm_apply q.val
  have hrad : ∀ w, Bpair u w = 0 := by
    intro w
    have h := (mem_paperSphericalCharacterRadical _ _ _ q.val).mp q.property (e w)
    rw [← hu, paperSlitCharacterSphere_jacobi] at h
    exact h
  obtain ⟨W, hW⟩ := pair_radical_has_fiber_preimage u hrad
  refine ⟨W, Subtype.ext ?_⟩
  change e (paperChainSlitEquiv m n j (fiberToSectorLin W)) = q.val
  rw [hW]
  exact hu

/-- The fiber-to-radical map is a linear equivalence, using the paper's local
elliptic/seam regularity route and finite-energy-to-boundedness theorem. -/
noncomputable def fiberSphereRadicalEquiv (m n j : ℕ) [NeZero m] :
    isotypicFiber 3 m j n ≃ₗ[ℂ]
      paperSphericalCharacterRadical ((n : ℝ) / m) j (surfacePotential 3) :=
  LinearEquiv.ofBijective fiberToSphereRadical
    ⟨fiberToSphereRadical_injective, fiberToSphereRadical_surjective⟩

theorem isotypicFiber_finrank_eq_radical (m n j : ℕ) [NeZero m] :
    Module.finrank ℂ (isotypicFiber 3 m j n) =
      Module.finrank ℂ (paperSphericalCharacterRadical ((n : ℝ) / m) j (surfacePotential 3)) :=
  (fiberSphereRadicalEquiv m n j).finrank_eq

end KsIndex.PaperSlitTransport
