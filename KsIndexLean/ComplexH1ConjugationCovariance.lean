module

/-
Complex conjugation commutes with disk rotation and boundary trace.

Rotation is measure-preserving precomposition, so it commutes with pointwise
conjugation on `L²` and with `conjH1` on the weak `H¹` carrier. Consequently,
conjugation sends `weakCharacterDomain θ c` to the domain with conjugate
character value, at the same rotation angle.

Radial profiles commute with conjugation almost everywhere. Continuity of their
radial representatives extends that identity to the boundary trace. The form
identities are supplied separately by `ComplexH1ConjugationForm`.
-/
public import KsIndexLean.ComplexH1Conjugation
public import KsIndexLean.WeakTransmissionDomains
public import KsIndexLean.JacobiWeakCharacters
public import KsIndexLean.DiskTrace

@[expose] public section


noncomputable section
open scoped Real
open MeasureTheory
namespace KsIndex.WeakH1
open TauCeti KsIndex.Trace

/-- **`diskLpRotation` commutes with `star`** (rotation is measure-preserving precomposition,
`star` is pointwise conjugation). -/
lemma diskLpRotation_star (θ : ℝ) (g : L2C) :
    diskLpRotation θ (star g) = star (diskLpRotation θ g) := by
  apply Lp.ext
  filter_upwards [diskLpRotation_coe_ae θ (star g),
    (measurePreserving_planeRotation_disk θ).quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_star g),
    Lp.coeFn_star (diskLpRotation θ g), diskLpRotation_coe_ae θ g]
    with x hx1 hxs hxsr hx2
  simp only [Function.comp_apply, Pi.star_apply] at hx1 hxs hxsr hx2 ⊢
  rw [hx1, hxs, hxsr, hx2]

/-- **`diskRotation` commutes with conjugation** (value covariance + `diskLpRotation_star`). -/
lemma diskRotation_conjH1 (θ : ℝ) (u : ComplexH1) :
    diskRotation θ (conjH1 u) = conjH1 (diskRotation θ u) := by
  apply valueCLM_injective
  have hL : valueCLM (diskRotation θ (conjH1 u)) = diskLpRotation θ (star (valueCLM u)) := by
    rw [show diskRotation θ (conjH1 u) = diskH1Rotation θ (conjH1 u) from rfl,
      diskH1Rotation_value, valueCLM_conjH1]
  have hR : valueCLM (conjH1 (diskRotation θ u)) = star (diskLpRotation θ (valueCLM u)) := by
    rw [valueCLM_conjH1, show diskRotation θ u = diskH1Rotation θ u from rfl, diskH1Rotation_value]
  rw [hL, hR, diskLpRotation_star]

/-- **Conjugation maps the character domain to its conjugate eigenvalue.** -/
lemma conjH1_mem_weakCharacter (θ : ℝ) (c : ℂ) {u : ComplexH1}
    (hu : u ∈ weakCharacterDomain θ c) :
    conjH1 u ∈ weakCharacterDomain θ ((starRingEnd ℂ) c) := by
  rw [mem_weakCharacterDomain] at hu ⊢
  rw [diskRotation_conjH1, hu, map_smulₛₗ]

/-! ### Boundary-trace covariance -/

/-- `sliceLp` commutes with `star` (pointwise conjugation of the slice). -/
lemma sliceLp_star_ae {a b : ℝ} (ha : 0 < a) {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (annulusSet a b))) :
    sliceLp a b (star u) =ᵐ[volume.restrict (Set.Ioo a b)] star (sliceLp a b u) := by
  filter_upwards [sliceLp_coe_ae ha hu, sliceLp_coe_ae ha hu.star] with t ht hstar
  apply Lp.ext
  filter_upwards [ht, hstar, Lp.coeFn_star (sliceLp a b u t)] with w hw hstarw hc
  change sliceLp a b (star u) t w = (star (sliceLp a b u t)) w
  rw [hc, Pi.star_apply, hw, hstarw]
  rfl

/-- **Radial profile covariance:** conjugation on `ComplexH1` conjugates the disk profile. -/
lemma diskProfile_conjH1_ae (u : ComplexH1) :
    diskProfile (conjH1 u)
      =ᵐ[volume.restrict (Set.Ioo (1 / 2 : ℝ) 1)] fun t => star (diskProfile u t) := by
  have h := Lp.coeFn_star (valueCLM u)
  have hc := h.filter_mono (ae_mono (Measure.restrict_mono collar_subset_disk le_rfl))
  dsimp only [diskProfile]
  rw [valueCLM_conjH1]
  filter_upwards [sliceLp_congr_ae (by norm_num : (0 : ℝ) < 1 / 2) hc,
    sliceLp_star_ae (by norm_num) (collar_memLp (valueCLM u))] with t ht hs
  exact ht.trans hs

/-- `star` is norm-preserving on the circle `L²`. -/
lemma norm_star_circleLp (f : Lp ℂ 2 circleMeasure) : ‖star f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_star f)]
  congr 1
  exact eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable f).star
    (Lp.aestronglyMeasurable f) (Filter.Eventually.of_forall fun x => by simp)

/-- `star` is additive on the circle `L²` (the `StarAddMonoid` instance is not registered for
`Lp`, so this is proven pointwise). -/
lemma star_sub_circleLp (f g : Lp ℂ 2 circleMeasure) : star (f - g) = star f - star g := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (f - g), Lp.coeFn_sub f g,
    Lp.coeFn_sub (star f) (star g), Lp.coeFn_star f, Lp.coeFn_star g] with x h1 h2 h3 h4 h5
  simp only [h1, h2, h3, h4, h5, Pi.star_apply, Pi.sub_apply, star_sub]

/-- `star` is continuous on the circle `L²` (it is an isometry). -/
lemma continuous_star_circleLp :
    Continuous (star : Lp ℂ 2 circleMeasure → Lp ℂ 2 circleMeasure) := by
  have hiso : Isometry (star : Lp ℂ 2 circleMeasure → Lp ℂ 2 circleMeasure) := by
    refine Isometry.of_dist_eq (fun f g => ?_)
    rw [dist_eq_norm, dist_eq_norm, ← star_sub_circleLp, norm_star_circleLp]
  exact hiso.continuous

/-- **Boundary trace covariance:** conjugation on `ComplexH1` is `star` on the boundary trace. -/
lemma diskTrace_conjH1 (u : ComplexH1) : diskTrace (conjH1 u) = star (diskTrace u) := by
  have he := eqOn_Icc_of_ae_eq (by norm_num : (1 / 2 : ℝ) < 1)
    (diskRepresentative_continuousOn (conjH1 u))
    (continuous_star_circleLp.comp_continuousOn (diskRepresentative_continuousOn u))
  apply he ?_ (by norm_num)
  filter_upwards [diskRepresentative_ae (conjH1 u), diskRepresentative_ae u,
    diskProfile_conjH1_ae u] with t hs hu hc
  rw [← hs]
  simp only [Function.comp_apply]
  rw [← hu]
  exact hc

/-- **`diskTraceCLM` covariance.** -/
lemma diskTraceCLM_conjH1 (u : ComplexH1) :
    diskTraceCLM (conjH1 u) = star (diskTraceCLM u) := by
  simp only [diskTraceCLM_apply]; exact diskTrace_conjH1 u

end KsIndex.WeakH1
