module

public import KsIndexLean.CircleQPhysicalDomain

@[expose] public section


/-! The physical DtN form and its coefficient normalization. -/
noncomputable section
namespace KsIndex.CircleQ
open CircleSobolev PaperSlitAdapter SectorReduce Sector SectorForm DtnBridge

/-- The circle DtN form on the sign-multiplier graph domain. On the positive
character subspace the two terms use the DtN restrictions to the residue
classes `1 + 6ℤ` and `4 + 6ℤ`, respectively. Each class contains frequencies
of both signs. Duality uses arclength measure. -/
def physicalForm (s : ℝ) (q r : ↥sigmaGraph) : ℂ :=
  duality (1 / 2 : ℝ) (dtnCLM 3 (q : SigmaGraphAmbient).fst)
    (r : SigmaGraphAmbient).fst +
  (s : ℂ) ^ 2 * duality (1 / 2 : ℝ) (dtnCLM 3 (q : SigmaGraphAmbient).snd)
    (r : SigmaGraphAmbient).snd

/-- Reconstructed traces identify the physical DtN duality with the sector form. -/
theorem duality_dtn_traceOfSector (u v : Idx → ℂ) (hu : MemSector u) (hv : MemSector v) :
    duality (1 / 2 : ℝ) (dtnCLM 3 (traceOfSector u hu).val)
      (traceOfSector v hv).val = (2 * Real.pi : ℂ) * bN3 u v := by
  change duality _ (dottedDtnCLM 3 (traceOfSector u hu)).val _ = _
  rw [duality_dottedDtnCLM,
    ← bN3_sectorOfTrace_eq_faithfulDtnB _ _ (traceOfSector_class_support v hv),
    sectorOfTrace_traceOfSector, sectorOfTrace_traceOfSector]

/-- The physical form is `2π` times the coefficient form, with the same parameter. -/
theorem physicalForm_eq_Bform (s : ℝ) (u v : ℤ → ℂ) (hu : MemDom u) (hv : MemDom v) :
    physicalForm s (physicalGraph u hu) (physicalGraph v hv) =
      (2 * Real.pi : ℂ) * Statements.Bform s u v := by
  unfold physicalForm physicalGraph
  rw [domPair_fst, domPair_fst, domPair_snd, domPair_snd,
    sigmaLift_traceOfSector (iotaTan_mem_Domς 0 hu),
    sigmaLift_traceOfSector (iotaTan_mem_Domς 0 hv),
    duality_dtn_traceOfSector, duality_dtn_traceOfSector,
    sgn_iotaTan 0 (summable_normSq hu.1), sgn_iotaTan 0 (summable_normSq hv.1)]
  simp only [bN3, iotaTan_inl, iotaTan_inr, coefT, zero_mul, Real.sin_zero,
    Real.cos_zero, zero_div, Complex.ofReal_zero, mul_zero, map_zero, tsum_zero,
    add_zero, zero_add, Sum.elim_inl, Sum.elim_inr]
  unfold Statements.Bform
  ring

/-- Unnormalized physical mass, in the same convention as the DtN form. -/
theorem physicalTrace_inner (u v : ℤ → ℂ) (hu : MemDom u) (hv : MemDom v) :
    inner ℂ (physicalTrace u hu) (physicalTrace v hv) =
      (2 * Real.pi : ℂ) * Statements.massPair u v := by
  have hm := physicalTrace_mass u v hu hv
  have hp : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by positivity : 0 < 2 * Real.pi))
  have hm' : Statements.massPair u v = (2 * Real.pi : ℂ)⁻¹ *
      inner ℂ (physicalTrace u hu) (physicalTrace v hv) := by
    simpa only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul,
      Complex.ofReal_ofNat] using hm
  rw [hm', mul_inv_cancel_left₀ hp]

/-- A coefficient eigen-equation transports against every physical test in the
positive graph domain, with no change to its eigenvalue. -/
theorem physicalForm_eigen_equation (s mu : ℝ) (u : ℤ → ℂ) (hu : MemDom u)
    (he : ∀ v : ℤ → ℂ, MemDom v →
      Statements.Bform s v u = (mu : ℂ) * Statements.massPair v u)
    (f : Space (1 / 2 : ℝ)) (hf : MemDomSigma f)
    (hp : f ∈ character (1 / 2 : ℝ) (-1) 6) :
    physicalForm s (domPair f hf) (physicalGraph u hu) =
      inner ℂ (toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2) f)
        ((mu : ℂ) • physicalTrace u hu) := by
  obtain ⟨v, hv, hrec⟩ := exists_physical_reconstruction f hf hp
  subst f
  change physicalForm s (physicalGraph v hv) (physicalGraph u hu) =
    inner ℂ (physicalTrace v hv) ((mu : ℂ) • physicalTrace u hu)
  rw [physicalForm_eq_Bform, he v hv, inner_smul_right, physicalTrace_inner]
  ring

end KsIndex.CircleQ
