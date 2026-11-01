module

public import KsIndexLean.DiskH1Rotation

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma rotatedColumn_energy (θ : ℝ) (u : ComplexH1) :
    ‖rotatedColumn θ u 1‖ ^ 2 + ‖rotatedColumn θ u Complex.I‖ ^ 2 =
      ‖dxLp u‖ ^ 2 + ‖dyLp u‖ ^ 2 := by
  have hi (f : L2C) : Integrable (fun z => ‖f z‖ ^ 2) (volume.restrict (disk : Set ℂ)) :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp f).aestronglyMeasurable).mp (Lp.memLp f)
  simp only [lp_norm_sq]
  rw [← integral_add (hi _) (hi _), ← integral_add (hi _) (hi _)]
  calc
    _ = ∫ z, (‖dxLp u (planeRotation θ z)‖ ^ 2 + ‖dyLp u (planeRotation θ z)‖ ^ 2)
        ∂volume.restrict (disk : Set ℂ) := by
      apply integral_congr_ae
      filter_upwards [rotatedColumn_coe_ae θ u 1, rotatedColumn_coe_ae θ u Complex.I]
        with z hx hy
      rw [hx, hy, planeRotation_derivative_energy, Dxy_one, Dxy_I]
    _ = _ := (measurePreserving_planeRotation_disk θ).integral_comp
      (planeRotation θ).toHomeomorph.measurableEmbedding
      (fun z => ‖dxLp u z‖ ^ 2 + ‖dyLp u z‖ ^ 2)

theorem diskH1Rotation_norm (θ : ℝ) (u : ComplexH1) : ‖diskH1Rotation θ u‖ = ‖u‖ := by
  have h : ‖diskH1Rotation θ u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [coordinate_graph_norm_sq, coordinate_graph_norm_sq,
      diskH1Rotation_value, (diskLpRotation θ).norm_map,
      (diskH1Rotation_coordinates θ u).1, (diskH1Rotation_coordinates θ u).2]
    linarith [rotatedColumn_energy θ u]
  nlinarith [norm_nonneg (diskH1Rotation θ u), norm_nonneg u]

/-- Same-sign rotation on the adopted weak H¹ carrier, with its actual graph norm. -/
def diskRotation (θ : ℝ) : ComplexH1 →ₗᵢ[ℂ] ComplexH1 where
  toLinearMap :=
    { toFun := diskH1Rotation θ
      map_add' := diskH1Rotation_add θ
      map_smul' := diskH1Rotation_smul θ }
  norm_map' := diskH1Rotation_norm θ

lemma planeRotation_zero : planeRotation 0 = LinearIsometryEquiv.refl ℝ ℂ := by
  ext z
  simp [planeRotation_apply]

lemma planeRotation_add_apply (α β : ℝ) (z : ℂ) :
    planeRotation (α + β) z = planeRotation α (planeRotation β z) := by
  simp [planeRotation_apply, add_mul, Complex.exp_add, mul_assoc]

lemma diskLpRotation_zero (f : L2C) : diskLpRotation 0 f = f := by
  change Lp.compMeasurePreserving (planeRotation 0) _ f = f
  have h : (planeRotation 0 : ℂ → ℂ) = id := by ext z; simp [planeRotation_apply]
  simp only [h, Lp.compMeasurePreserving_id_apply]

lemma diskLpRotation_add (α β : ℝ) (f : L2C) :
    diskLpRotation (α + β) f = diskLpRotation α (diskLpRotation β f) := by
  change Lp.compMeasurePreserving (planeRotation (α + β)) _ f =
    Lp.compMeasurePreserving (planeRotation α) _ (Lp.compMeasurePreserving (planeRotation β) _ f)
  have h : (planeRotation (α + β) : ℂ → ℂ) = planeRotation β ∘ planeRotation α := by
    ext z
    rw [add_comm, planeRotation_add_apply]
    rfl
  simpa only [h] using Lp.compMeasurePreserving_comp_apply f
    (measurePreserving_planeRotation_disk β) (measurePreserving_planeRotation_disk α)

lemma diskRotation_zero (u : ComplexH1) : diskRotation 0 u = u := by
  apply valueCLM_injective
  change valueCLM (diskH1Rotation 0 u) = _
  rw [diskH1Rotation_value, diskLpRotation_zero]

lemma diskRotation_add (α β : ℝ) (u : ComplexH1) :
    diskRotation (α + β) u = diskRotation α (diskRotation β u) := by
  apply valueCLM_injective
  change valueCLM (diskH1Rotation (α + β) u) = valueCLM (diskH1Rotation α (diskH1Rotation β u))
  rw [diskH1Rotation_value, diskH1Rotation_value, diskH1Rotation_value, diskLpRotation_add]

lemma diskRotation_neg (θ : ℝ) (u : ComplexH1) : diskRotation (-θ) (diskRotation θ u) = u := by
  rw [← diskRotation_add, neg_add_cancel, diskRotation_zero]

end KsIndex.Trace
