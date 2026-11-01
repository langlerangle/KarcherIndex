module

public import KsIndexLean.PaperExactFiberNullity

@[expose] public section


/-! Nullity at the two threshold phases. The reverse regularity correspondence
identifies sector radicals with bounded chain Jacobi fields. At an interior
sampled phase, the two nontrivial rotation characters each contribute one
exactly at a threshold; the trivial character contributes zero. -/
noncomputable section
open Classical
namespace KsIndex.PaperSlitTransport
open KsIndex.NullityDecomp KsIndex.Staircase

lemma circle_nullity_eq_threshold_indicator {s : ℝ} (hs : 0 < s) :
    Statements.nul s = if s = sstar then 1 else 0 := by
  by_cases he : s = sstar
  · subst s
    rw [ite_eq_left rfl]
    exact (Statements.nul_eq_one_iff hs).mpr sstar_spec.2.1
  · rw [ite_eq_right he]
    exact nul_eq_zero_of_ne hs he

lemma tan_half_pos {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    0 < Real.tan (α * Real.pi / 2) := by
  have hx0 : 0 < α * Real.pi / 2 := by positivity
  have hx1 : α * Real.pi / 2 < Real.pi / 2 := by
    nlinarith [Real.pi_pos, mul_pos (show 0 < 1 - α by linarith) Real.pi_pos]
  rw [Real.tan_eq_sin_div_cos]
  exact div_pos (Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith [Real.pi_pos]))
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hx1⟩)

/-- The two threshold phases are distinct, so exactly one circle summand
contributes at either endpoint and neither contributes elsewhere. -/
theorem sector_nullity_eq_endpoint_indicator {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    FormIndex.formNullity (SectorForm.NBform α) Sector.Domς =
      if α = alphaStar ∨ α = 1 - alphaStar then 1 else 0 := by
  rw [SectorPhase.sector_nullity_eq α h0 h1,
    circle_nullity_eq_threshold_indicator (tan_half_pos h0 h1),
    circle_nullity_eq_threshold_indicator (tan_half_pos (by linarith) (by linarith))]
  have ht := tan_half_eq_sstar_iff h0 h1
  have ht' := tan_half_eq_sstar_iff (show 0 < 1 - α by linarith) (show 1 - α < 1 by linarith)
  have he : 1 - α = 1 - alphaStar ↔ α = alphaStar := by constructor <;> intro h <;> linarith
  simp only [ht, ht', he]
  have hne : alphaStar ≠ 1 - alphaStar := by linarith [alphaStar_lt_half]
  by_cases ha : α = alphaStar
  · have hb : α ≠ 1 - alphaStar := by simpa only [ha] using hne
    simp [ha, hne]
  · by_cases hb : α = 1 - alphaStar <;> simp [ha, hb, Ne.symm hne]

/-- Each nontrivial character contributes one at either threshold, zero elsewhere. -/
theorem isotypicFiber_interior_finrank_endpoint {m r a : ℕ} [NeZero m]
    (ha0 : 0 < a) (ham : a < m) (hr : PaperSlitAdapter.SectorClass r) :
    (Module.finrank ℂ (isotypicFiber 3 m r a) : ℕ∞) =
      if (a : ℝ) / m = alphaStar ∨ (a : ℝ) / m = 1 - alphaStar then 1 else 0 := by
  rw [isotypicFiber_interior_nullity_eq_sector ha0 ham hr]
  apply sector_nullity_eq_endpoint_indicator
  · exact div_pos (by exact_mod_cast ha0) (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m))
  · apply (div_lt_one (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m))).mpr
    exact_mod_cast ham

/-- An interior sampled phase contributes exactly two at resonance and zero
otherwise: the trivial character vanishes and each other character contributes one. -/
theorem interiorPhase_total_eq_endpoint {m a : ℕ} [NeZero m]
    (ha0 : 0 < a) (ham : a < m) :
    (∑ r : Fin 3, Cardinal.toENat (Module.rank ℂ (isotypicFiber 3 m (r : ℕ) a))) =
      if (a : ℝ) / m = alphaStar ∨ (a : ℝ) / m = 1 - alphaStar then 2 else 0 := by
  simp_rw [isotypicFiber_rank_toENat]
  rw [Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one]
  change ((Module.finrank ℂ (isotypicFiber 3 m 0 a) : ℕ∞) +
    (Module.finrank ℂ (isotypicFiber 3 m 1 a) : ℕ∞)) +
    (Module.finrank ℂ (isotypicFiber 3 m 2 a) : ℕ∞) = _
  rw [isotypicFiber_interior_r0_finrank_zero ha0 ham,
    isotypicFiber_interior_finrank_endpoint ha0 ham (show PaperSlitAdapter.SectorClass 1 by norm_num [PaperSlitAdapter.SectorClass]),
    isotypicFiber_interior_finrank_endpoint ha0 ham (show PaperSlitAdapter.SectorClass 2 by norm_num [PaperSlitAdapter.SectorClass])]
  split_ifs <;> norm_num

end KsIndex.PaperSlitTransport
