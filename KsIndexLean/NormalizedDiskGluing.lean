module

public import KsIndexLean.SeamRepresentativeCompatibility
public import KsIndexLean.SmoothRepresentativeEnergy

@[expose] public section


/-! Raw disk representatives with explicitly assigned circle values and zero
exterior. Their joined field agrees with the smooth seam representative. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Keep the interior representative, assign its circle values, and zero the exterior. -/
def filledDisk (f b : ℂ → ℂ) (z : ℂ) : ℂ :=
  if ‖z‖ < 1 then f z else if ‖z‖ = 1 then b z else 0

lemma filledDisk_eq_interior (f b : ℂ → ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    filledDisk f b z = f z := by simp only [filledDisk, ite_eq_left hz]

lemma filledDisk_eq_boundary (f b : ℂ → ℂ) {z : ℂ} (hz : ‖z‖ = 1) :
    filledDisk f b z = b z := by simp [filledDisk, hz]

lemma filledDisk_eq_exterior (f b : ℂ → ℂ) {z : ℂ} (hz : 1 < ‖z‖) :
    filledDisk f b z = 0 := by
  simp only [filledDisk, ite_eq_right (not_lt.mpr hz.le), ite_eq_right (ne_of_gt hz)]

lemma filledDisk_eqOn_disk (f b : ℂ → ℂ) : EqOn (filledDisk f b) f (WeakH1.disk : Set ℂ) := by
  intro z hz
  exact filledDisk_eq_interior f b (by simpa only [dist_zero_right] using (Metric.mem_ball.mp hz))

lemma filledDisk_smooth_interior {f : ℂ → ℂ} (b : ℂ → ℂ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (WeakH1.disk : Set ℂ)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (filledDisk f b) (WeakH1.disk : Set ℂ) :=
  hf.congr (filledDisk_eqOn_disk f b)

lemma filledDisk_value_ae (u : ComplexH1) {f : ℂ → ℂ} (b : ℂ → ℂ)
    (ha : valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] f) :
    valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] filledDisk f b := by
  filter_upwards [ha, ae_restrict_mem WeakH1.disk.isOpen.measurableSet] with z hz hzd
  exact hz.trans ((filledDisk_eqOn_disk f b) hzd).symm

/-- The ordinary phase join used by a disk pair. -/
def filledJoin (c : ℂ) (f g b d : ℂ → ℂ) (z : ℂ) : ℂ :=
  if ‖z‖ ≤ 1 then filledDisk f b z else c * filledDisk g d (Bracket.σ z)

/-- Assigning the seam representative's circle values makes the actual raw
join equal to that smooth representative on the entire seam domain. -/
lemma filledJoin_eqOn_seamDomain {A : Set Circle₁} (hA : IsOpen A)
    (c : ℂ) (f g b d F : ℂ → ℂ)
    (hi : EqOn F f (annulusSet (1 / 2 : ℝ) 1))
    (ho : EqOn F (fun z => c * g (Bracket.σ z)) (annulusSet 1 2))
    (hb : ∀ w : Circle₁, w ∈ A → b w = F w) :
    EqOn (filledJoin c f g b d) F (seamDomain A hA : Set ℂ) := by
  intro z hz
  by_cases hn : ‖z‖ ≤ 1
  · rw [filledJoin, ite_eq_left hn]
    rcases lt_or_eq_of_le hn with hlt | heq
    · rw [filledDisk_eq_interior f b hlt]
      exact (hi ⟨hz.1.1, hlt⟩).symm
    · rw [filledDisk_eq_boundary f b heq]
      let w : Circle₁ := ⟨z, mem_sphere_zero_iff_norm.mpr heq⟩
      apply hb w
      by_contra hw
      exact hz.2 ⟨w, hw, rfl⟩
  · rw [filledJoin, ite_eq_right hn]
    have hσ := sigma_mem_disk_of_one_lt_norm (lt_of_not_ge hn)
    rw [(filledDisk_eqOn_disk g d) hσ]
    exact (ho ⟨lt_of_not_ge hn, hz.1.2⟩).symm

lemma filledJoin_smooth_on_seamDomain {A : Set Circle₁} (hA : IsOpen A)
    (c : ℂ) (f g b d F : ℂ → ℂ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (seamDomain A hA : Set ℂ))
    (hi : EqOn F f (annulusSet (1 / 2 : ℝ) 1))
    (ho : EqOn F (fun z => c * g (Bracket.σ z)) (annulusSet 1 2))
    (hb : ∀ w : Circle₁, w ∈ A → b w = F w) :
    ContDiffOn ℝ (⊤ : ℕ∞) (filledJoin c f g b d) (seamDomain A hA : Set ℂ) :=
  hF.congr (filledJoin_eqOn_seamDomain hA c f g b d F hi ho hb)

end KsIndex.Trace
