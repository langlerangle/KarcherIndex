module

public import KsIndexLean.WeakReflectionExtension

@[expose] public section


/-! Unrestricted weak reflection across the entire disk boundary. -/
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.SingleDisk

@[simp] theorem seamDomain_univ :
    seamDomain (Set.univ : Set Circle₁) isOpen_univ = annulusOpens (1 / 2) 2 := by
  apply Opens.ext
  change annulusSet (1 / 2 : ℝ) 2 \ Subtype.val '' (Set.univ : Set Circle₁)ᶜ = annulusSet (1 / 2 : ℝ) 2
  simp

/-- Every weak disk H1 function extends weakly across its whole boundary.
No zero-trace or phase hypothesis is required. The domain here is an annulus;
the central disk must be attached separately for a bulk extension operator. -/
theorem full_boundary_even_extension (u : ComplexH1) :
    TauCeti.HasWeakFDerivOn volume (annulusOpens (1 / 2) 2)
      (refl 1 (valueCLM u)) (joinedDiskJet u u 1) := by
  simpa only [seamDomain_univ] using
    (weak_even_extension (A := Set.univ) isOpen_univ u)

theorem full_boundary_even_value_memLp (u : ComplexH1) :
    MemLp (refl 1 (valueCLM u)) 2
      (volume.restrict (annulusSet (1 / 2 : ℝ) 2)) := by
  have h := refl_value_memLp (A := Set.univ) isOpen_univ u 1
  simpa only [seamDomain_univ] using h

theorem full_boundary_even_direction_memLp (u : ComplexH1) (d : ℂ) :
    MemLp (fun z => joinedDiskJet u u 1 z d) 2
      (volume.restrict (annulusSet (1 / 2 : ℝ) 2)) := by
  have h := refl_direction_memLp (A := Set.univ) isOpen_univ u 1 d
  simpa only [seamDomain_univ] using h

/-- The reflected value agrees with the original function throughout the disk. -/
lemma full_boundary_even_eq_inner (u : ComplexH1) {z : ℂ} (hz : ‖z‖ < 1) :
    refl 1 (valueCLM u) z = valueCLM u z := by
  simp only [KsIndex.SingleDisk.refl, ite_eq_left hz.le]

/-- Cartesian derivatives give the extension its regular jet at the center. -/
theorem full_boundary_even_inner_weak (u : ComplexH1) :
    TauCeti.HasWeakFDerivOn volume disk (refl 1 (valueCLM u))
      (Dxy (dxLp u) (dyLp u)) := by
  apply (carrier_hasJet u).congr_ae
  filter_upwards [ae_restrict_mem disk.isOpen.measurableSet] with z hz
  exact (full_boundary_even_eq_inner u (KsIndex.SurfaceForm.mem_disk_iff.mp hz)).symm

/-- The Cartesian and reflected jets coincide on their actual overlapping collar. -/
theorem full_boundary_even_jet_overlap (u : ComplexH1) :
    Dxy (dxLp u) (dyLp u) =ᵐ[volume.restrict (annulusSet (1 / 2 : ℝ) 1)]
      joinedDiskJet u u 1 := by
  have hi := (full_boundary_even_inner_weak u).mono
    (show annulusOpens (1 / 2) 1 ≤ disk from fun z hz =>
      KsIndex.SurfaceForm.mem_disk_iff.mpr hz.2)
  have ho := (full_boundary_even_extension u).mono
    (show annulusOpens (1 / 2) 1 ≤ annulusOpens (1 / 2) 2 from
      fun z hz => ⟨hz.1, lt_trans hz.2 (by norm_num)⟩)
  exact hi.ae_eq ho

end KsIndex.Trace
