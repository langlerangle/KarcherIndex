module

public import KsIndexLean.CirclePowerCover

@[expose] public section


/-! Representative-safe L2 pullback with the paper's phase. -/
noncomputable section
open MeasureTheory
namespace KsIndex.Trace

lemma memLp_phased_circlePower {k : ℕ} (hk : 0 < k) (c : ℕ)
    (g : Lp ℂ 2 circleMeasure) :
    MemLp (fun w : Circle₁ => (w : ℂ)^c * g (circlePower k w)) 2 circleMeasure := by
  have h := (Lp.memLp g).comp_measurePreserving (measurePreserving_circlePower hk)
  apply h.of_le_mul (c := 1)
    (((continuous_subtype_val.pow c).aestronglyMeasurable).mul h.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun w => by
    have hw : ‖(w : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp w.property
    simp [norm_pow, hw]

def phasedPowerL2 {k : ℕ} (hk : 0 < k) (c : ℕ)
    (g : Lp ℂ 2 circleMeasure) : Lp ℂ 2 circleMeasure :=
  (memLp_phased_circlePower hk c g).toLp _

lemma phasedPowerL2_ae {k : ℕ} (hk : 0 < k) (c : ℕ)
    (g : Lp ℂ 2 circleMeasure) :
    phasedPowerL2 hk c g =ᵐ[circleMeasure]
      (fun w : Circle₁ => (w : ℂ)^c * g (circlePower k w)) :=
  (memLp_phased_circlePower hk c g).coeFn_toLp

lemma phasedPowerL2_add {k : ℕ} (hk : 0 < k) (c : ℕ)
    (f g : Lp ℂ 2 circleMeasure) :
    phasedPowerL2 hk c (f + g) = phasedPowerL2 hk c f + phasedPowerL2 hk c g := by
  apply Lp.ext
  have ha := (measurePreserving_circlePower hk).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_add f g)
  filter_upwards [phasedPowerL2_ae hk c (f + g), phasedPowerL2_ae hk c f,
    phasedPowerL2_ae hk c g, ha,
    Lp.coeFn_add (phasedPowerL2 hk c f) (phasedPowerL2 hk c g)] with w h hf hg ha hs
  simpa only [Pi.add_apply, Function.comp_apply, h, hs, hf, hg, mul_add] using
    congrArg (fun z : ℂ => (w : ℂ)^c * z) ha

lemma phasedPowerL2_smul {k : ℕ} (hk : 0 < k) (c : ℕ)
    (a : ℂ) (g : Lp ℂ 2 circleMeasure) :
    phasedPowerL2 hk c (a • g) = a • phasedPowerL2 hk c g := by
  apply Lp.ext
  have ha := (measurePreserving_circlePower hk).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_smul a g)
  filter_upwards [phasedPowerL2_ae hk c (a • g), phasedPowerL2_ae hk c g, ha,
    Lp.coeFn_smul a (phasedPowerL2 hk c g)] with w h hg ha hs
  simp only [Pi.smul_apply, Function.comp_apply] at ha hs
  rw [h, hs, hg, ha]
  exact mul_smul_comm _ _ _

lemma norm_phasedPowerL2 {k : ℕ} (hk : 0 < k) (c : ℕ)
    (g : Lp ℂ 2 circleMeasure) : ‖phasedPowerL2 hk c g‖ = ‖g‖ := by
  let q := Lp.compMeasurePreserving (circlePower k) (measurePreserving_circlePower hk) g
  have he : ∀ᵐ w ∂circleMeasure, ‖phasedPowerL2 hk c g w‖ = ‖q w‖ := by
    filter_upwards [phasedPowerL2_ae hk c g,
      Lp.coeFn_compMeasurePreserving g (measurePreserving_circlePower hk)] with w h hq
    have hw : ‖(w : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp w.property
    simp only [h, norm_mul, norm_pow, hw, one_pow, one_mul]
    exact congrArg norm hq.symm
  have h1 : ‖phasedPowerL2 hk c g‖ ≤ 1 * ‖q‖ :=
    Lp.norm_le_mul_norm_of_ae_le_mul (he.mono fun _ h => by simp [h])
  have h2 : ‖q‖ ≤ 1 * ‖phasedPowerL2 hk c g‖ :=
    Lp.norm_le_mul_norm_of_ae_le_mul (he.mono fun _ h => by simp [h])
  have hq : ‖q‖ = ‖g‖ := Lp.norm_compMeasurePreserving g _
  linarith

/-- The phased covering is a linear isometry of the actual circle L2 space. -/
def phasedPowerLI {k : ℕ} (hk : 0 < k) (c : ℕ) :
    Lp ℂ 2 circleMeasure →ₗᵢ[ℂ] Lp ℂ 2 circleMeasure where
  toFun := phasedPowerL2 hk c
  map_add' := phasedPowerL2_add hk c
  map_smul' := phasedPowerL2_smul hk c
  norm_map' := norm_phasedPowerL2 hk c

/-- Exact arc-vanishing transport for the actual L2 equivalence classes. -/
theorem phasedPowerL2_arc_zero_iff {k : ℕ} (hk : 0 < k) (c p : ℕ)
    (g : Lp ℂ 2 circleMeasure) :
    (∀ᵐ w ∂circleMeasure.restrict (boundaryArc k p), phasedPowerL2 hk c g w = 0) ↔
    (∀ᵐ w ∂circleMeasure.restrict (boundaryArc 1 p), g w = 0) := by
  have he := ae_restrict_of_ae (s := boundaryArc k p) (phasedPowerL2_ae hk c g)
  have hi : (∀ᵐ w ∂circleMeasure.restrict (boundaryArc k p), phasedPowerL2 hk c g w = 0) ↔
      (∀ᵐ (w : Circle₁) ∂circleMeasure.restrict (boundaryArc k p),
        (w : ℂ)^c * g (circlePower k w) = 0) := by
    constructor
    · intro h
      filter_upwards [he, h] with w he h
      rwa [← he]
    · intro h
      filter_upwards [he, h] with w he h
      rwa [he]
  exact hi.trans (phased_circlePower_arc_zero_iff hk c p (Lp.stronglyMeasurable g).measurable)

end KsIndex.Trace
