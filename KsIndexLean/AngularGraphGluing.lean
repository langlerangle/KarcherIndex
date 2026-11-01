module

public import KsIndexLean.CommonAngularTests

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Transport an a.e. property through inversion using the proved null-set transport. -/
lemma ae_property_comp_inv_collar {P : ℝ → Prop}
    (h : ∀ᵐ t ∂volume.restrict (Ioo (1 / 2 : ℝ) 1), P t) :
    ∀ᵐ r ∂volume.restrict (Ioo (1 : ℝ) 2), P r⁻¹ := by
  have he : P =ᵐ[volume.restrict (Ioo (1 / 2 : ℝ) 1)] (fun _ => True) := by
    filter_upwards [h] with t ht
    exact propext (iff_true_intro ht)
  filter_upwards [ae_eq_comp_inv_collar he] with r hr
  exact of_eq_true hr

/-- A pairwise a.e. property patches across the single radial cut. -/
lemma ae_joinAt_pair_mem {E : Type*} {a c b : ℝ} {S : Set (E × E)}
    {f g p q : ℝ → E}
    (hl : ∀ᵐ t ∂volume.restrict (Ioo a c), (f t, g t) ∈ S)
    (hr : ∀ᵐ t ∂volume.restrict (Ioo c b), (p t, q t) ∈ S) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), (joinAt c f p t, joinAt c g q t) ∈ S := by
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mp hl,
    (ae_restrict_iff' measurableSet_Ioo).mp hr, volume.ae_ne c] with t hl' hr' htc ht
  by_cases hle : t ≤ c
  · simp only [joinAt, ite_eq_left hle]
    exact hl' ⟨ht.1, lt_of_le_of_ne hle htc⟩
  · simp only [joinAt, ite_eq_right hle]
    exact hr' ⟨lt_of_not_ge hle, ht.2⟩

/-- Radial inversion keeps the angular derivative's orientation and has no radial factor. -/
theorem inverted_disk_circleAngularGraph_ae (u : ComplexH1) (c : ℂ) :
    ∀ᵐ r ∂volume.restrict (Ioo (1 : ℝ) 2),
      (c • diskProfile u r⁻¹, c • diskAngularProfile u r⁻¹) ∈ circleAngularGraph := by
  filter_upwards [ae_property_comp_inv_collar (disk_circleAngularGraph_ae u)] with r hr
  exact circleAngularGraph.smul_mem c hr

/-- Angular graph membership survives radial joining, including a constant complex scalar.
No radial trace matching is needed for this angular-only assertion. -/
theorem joined_disk_circleAngularGraph_ae (u v : ComplexH1) (c : ℂ) :
    ∀ᵐ r ∂volume.restrict (Ioo (1 / 2 : ℝ) 2),
      (joinAt 1 (diskProfile u) (fun t => c • diskProfile v t⁻¹) r,
        joinAt 1 (diskAngularProfile u) (fun t => c • diskAngularProfile v t⁻¹) r)
        ∈ circleAngularGraph :=
  ae_joinAt_pair_mem (disk_circleAngularGraph_ae u) (inverted_disk_circleAngularGraph_ae v c)

end KsIndex.Trace
