module

public import KsIndexLean.CircleQPhysicalForm

@[expose] public section


/-! Boundedness of the physical circle form in the sign-multiplier graph norm. -/
noncomputable section
namespace KsIndex.CircleQ
open CircleSobolev

lemma physicalGraph_fst_norm_le (q : ↥sigmaGraph) :
    ‖(q : SigmaGraphAmbient).fst‖ ≤ ‖q‖ := by
  nlinarith [sigmaGraph_norm_sq q, sq_nonneg ‖(q : SigmaGraphAmbient).snd‖,
    norm_nonneg q, norm_nonneg (q : SigmaGraphAmbient).fst]

lemma physicalGraph_snd_norm_le (q : ↥sigmaGraph) :
    ‖(q : SigmaGraphAmbient).snd‖ ≤ ‖q‖ := by
  nlinarith [sigmaGraph_norm_sq q, sq_nonneg ‖(q : SigmaGraphAmbient).fst‖,
    norm_nonneg q, norm_nonneg (q : SigmaGraphAmbient).snd]

/-- An explicit finite bound on the full graph-domain form, hence also on its
positive character subspace. -/
theorem norm_physicalForm_le (s : ℝ) (q r : ↥sigmaGraph) :
    ‖physicalForm s q r‖ ≤
      (2 * Real.pi * ‖dtnCLM 3‖ * (1 + s ^ 2)) * ‖q‖ * ‖r‖ := by
  have hp (a b : Space (1 / 2 : ℝ)) :
      ‖duality (1 / 2 : ℝ) (dtnCLM 3 a) b‖ ≤
        (2 * Real.pi * ‖dtnCLM 3‖) * ‖a‖ * ‖b‖ := by
    calc
      _ ≤ (2 * Real.pi) * (‖dtnCLM 3 a‖ * ‖b‖) := norm_duality_le _ _ _
      _ ≤ (2 * Real.pi) * ((‖dtnCLM 3‖ * ‖a‖) * ‖b‖) := by
        gcongr
        exact (dtnCLM 3).le_opNorm a
      _ = _ := by ring
  have hfst : ‖duality (1 / 2 : ℝ) (dtnCLM 3 (q : SigmaGraphAmbient).fst)
      (r : SigmaGraphAmbient).fst‖ ≤
      (2 * Real.pi * ‖dtnCLM 3‖) * ‖q‖ * ‖r‖ := by
    refine (hp _ _).trans ?_
    gcongr
    · exact physicalGraph_fst_norm_le q
    · exact physicalGraph_fst_norm_le r
  have hsnd : ‖duality (1 / 2 : ℝ) (dtnCLM 3 (q : SigmaGraphAmbient).snd)
      (r : SigmaGraphAmbient).snd‖ ≤
      (2 * Real.pi * ‖dtnCLM 3‖) * ‖q‖ * ‖r‖ := by
    refine (hp _ _).trans ?_
    gcongr
    · exact physicalGraph_snd_norm_le q
    · exact physicalGraph_snd_norm_le r
  unfold physicalForm
  calc
    _ ≤ _ := norm_add_le _ _
    _ = ‖duality (1 / 2 : ℝ) (dtnCLM 3 (q : SigmaGraphAmbient).fst)
        (r : SigmaGraphAmbient).fst‖ + s ^ 2 *
        ‖duality (1 / 2 : ℝ) (dtnCLM 3 (q : SigmaGraphAmbient).snd)
        (r : SigmaGraphAmbient).snd‖ := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    _ ≤ (2 * Real.pi * ‖dtnCLM 3‖) * ‖q‖ * ‖r‖ +
        s ^ 2 * ((2 * Real.pi * ‖dtnCLM 3‖) * ‖q‖ * ‖r‖) :=
      add_le_add hfst (mul_le_mul_of_nonneg_left hsnd (sq_nonneg s))
    _ = _ := by ring

/-- Joint continuity in the graph topology, not the weaker half-order topology. -/
theorem continuous_physicalForm (s : ℝ) :
    Continuous (fun p : ↥sigmaGraph × ↥sigmaGraph => physicalForm s p.1 p.2) := by
  have hf : Continuous (fun q : ↥sigmaGraph => (q : SigmaGraphAmbient).fst) :=
    graphFstCLM.continuous.comp continuous_subtype_val
  have hg : Continuous (fun q : ↥sigmaGraph => (q : SigmaGraphAmbient).snd) :=
    graphSndCLM.continuous.comp continuous_subtype_val
  unfold physicalForm duality coefficientDuality
  exact ((continuous_const.mul (((dtnCLM 3).continuous.comp
    (hf.comp continuous_fst)).inner (hf.comp continuous_snd))).add
    (continuous_const.mul (continuous_const.mul (((dtnCLM 3).continuous.comp
      (hg.comp continuous_fst)).inner (hg.comp continuous_snd)))))

end KsIndex.CircleQ
