module

public import KsIndexLean.PaperRadicalFiberSurjective
public import KsIndexLean.ZeroPhaseNullity

@[expose] public section


/-! Exact sector counts on the `k = 3` chain carrier for nonzero natural periods `m`.
The fiber at phase `a / m` has the nullity of the weak pair form on
`paperSlitCharacterDomain`. At zero phase each of the three rotation characters
has dimension one. For `0 < a < m` and `SectorClass r`, the fiber nullity equals
the coefficient-sector form nullity. Summing the sampled phases and rotation
characters gives the chain nullity. The geometric EW identification is separate. -/
noncomputable section
namespace KsIndex.PaperSlitTransport
open KsIndex.Trace KsIndex.WeakH1 KsIndex.NullityDecomp KsIndex.Spectral
open KsIndex.PaperSlitAdapter KsIndex.DtnBridge

/-- Fiber dimension equals weak pair-form nullity at the sampled phase `a / m`. -/
theorem isotypicFiber_finrank_eq_pair_sesqNullity {m r a : ℕ} [NeZero m] :
    (Module.finrank ℂ (isotypicFiber 3 m r a) : ℕ∞) =
      sesqNullity (fun u v : paperSlitCharacterDomain ((a : ℝ) / m) r =>
        weakJacobi (surfacePotential 3) u.val.1 v.val.1 +
        weakJacobi (surfacePotential 3) u.val.2 v.val.2) := by
  rw [isotypicFiber_finrank_eq_radical]
  exact radical_finrank_eq_pair_sesqNullity _ _ _

/-- Each zero-phase rotation character contributes exactly one. -/
theorem isotypicFiber_zeroPhase_finrank_eq_one {m r : ℕ} [NeZero m] (hr : r < 3) :
    Module.finrank ℂ (isotypicFiber 3 m r 0) = 1 := by
  have h := isotypicFiber_finrank_eq_pair_sesqNullity (m := m) (r := r) (a := 0)
  have h0 := paperSlit_zeroPhase_nullity hr
  have hphase : ((0 : ℕ) : ℝ) / m = 0 := by simp
  rw [← hphase] at h0
  have he := h.trans h0
  exact_mod_cast he

/-- Both nontrivial rotation classes have precisely the paper sector nullity. -/
theorem isotypicFiber_interior_nullity_eq_sector {m r a : ℕ} [NeZero m]
    (ha0 : 0 < a) (ham : a < m) (hr : SectorClass r) :
    (Module.finrank ℂ (isotypicFiber 3 m r a) : ℕ∞) =
      FormIndex.formNullity (SectorForm.NBform ((a : ℝ) / m)) Sector.Domς := by
  rw [isotypicFiber_finrank_eq_pair_sesqNullity]
  apply paperSlit_nullity_eq_sectorClass _ _ _ hr
  · exact div_pos (by exact_mod_cast ha0) (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m))
  · apply (div_lt_one (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m))).mpr
    exact_mod_cast ham

/-- The original chain nullity equals the complete sum of the weak paper
sector counts, including resonant phases. -/
theorem nulSurface_eq_sum_paperSlit {m : ℕ} [NeZero m] :
    Surface.nulSurface 3 m = ∑ r : Fin 3, ∑ a : Fin m,
      sesqNullity (fun u v : paperSlitCharacterDomain ((a : ℝ) / m) (r : ℕ) =>
        weakJacobi (surfacePotential 3) u.val.1 v.val.1 +
        weakJacobi (surfacePotential 3) u.val.2 v.val.2) := by
  rw [nulSurface_eq_sum_isotypic 3 m (by norm_num) (Nat.pos_of_ne_zero (NeZero.ne m))]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro a _
  rw [isotypicFiber_rank_toENat]
  exact isotypicFiber_finrank_eq_pair_sesqNullity

end KsIndex.PaperSlitTransport
