module

public import KsIndexLean.AlphaStieltjesCompensated

@[expose] public section


/-! Backward interval transport for compensated power-arc groups. -/
noncomputable section
namespace KsIndex.PowerArc

/-- Coefficient of the next group value in the reversed recurrence. -/
def groupBackwardA (β r : ℝ) (n : ℕ) : ℝ :=
  ((n:ℝ)+9/2+1-(r-β)/2) / ((n:ℝ)+9/2+1-(r+β+2)/2)

/-- Factor multiplying the subtracted correction in the reversed recurrence. -/
def groupBackwardF (β r : ℝ) (n : ℕ) : ℝ :=
  (r*((n:ℝ)+9/2)+(r+β)/2) /
    (((n:ℝ)+9/2)^2*((n:ℝ)+9/2+1)^2*((n:ℝ)+9/2+1-(r+β+2)/2))

theorem compensatedPowerArcGroup_backward (β r κ w : ℝ) (n : ℕ)
    (hβ : 0 < β) (hβ1 : β < 1) (hr : β ≤ r)
    (hd : (n:ℝ)+9/2+1-(r-β)/2 ≠ 0)
    (ha : (n:ℝ)+9/2+1-(r+β+2)/2 ≠ 0) :
    compensatedPowerArcGroup β r κ w n =
      groupBackwardA β r n * compensatedPowerArcGroup β r κ w (n+1) -
        groupBackwardF β r n * stieltjesCorrectionD β r κ := by
  have alg (a d z t D v : ℝ) (ha : a ≠ 0) (hd : d ≠ 0)
      (hz : z ≠ 0) (hz1 : z+1 ≠ 0) :
      v = d/a*(a/d*v+D*t/(z^2*(z+1)^2*d))-t/(z^2*(z+1)^2*a)*D := by
    field_simp
    ring
  have hs := compensatedPowerArcGroup_step β r κ w n hβ hβ1 hr hd
  rw [hs]
  exact alg _ _ _ _ _ _ ha hd (by positivity) (by positivity)

/-- A nonnegative backward coefficient and forcing factor give signed interval transport. -/
theorem backward_interval (G Gnext D A F lo hi dlo dhi : ℝ)
    (he : G = A*Gnext-F*D) (hA : 0 ≤ A) (hF : 0 ≤ F)
    (hlo : lo ≤ Gnext) (hhi : Gnext ≤ hi) (hdlo : dlo ≤ D) (hdhi : D ≤ dhi) :
    A*lo-F*dhi ≤ G ∧ G ≤ A*hi-F*dlo := by
  rw [he]
  constructor
  · exact sub_le_sub (mul_le_mul_of_nonneg_left hlo hA)
      (mul_le_mul_of_nonneg_left hdhi hF)
  · exact sub_le_sub (mul_le_mul_of_nonneg_left hhi hA)
      (mul_le_mul_of_nonneg_left hdlo hF)

/-- For the four groups, the backward coefficients have fixed positive signs
throughout the finite window beginning at mode four. -/
theorem groupBackward_nonneg (β r : ℝ) (n : ℕ)
    (hβ : 0 < β) (hβ1 : β < 1) (hr : 0 ≤ r) (hr15 : r ≤ 15) (hn : 4 ≤ n) :
    0 ≤ groupBackwardA β r n ∧ 0 ≤ groupBackwardF β r n := by
  have hnR : (4:ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 < (n:ℝ)+9/2+1-(r+β+2)/2 := by linarith
  have hd : 0 < (n:ℝ)+9/2+1-(r-β)/2 := by linarith
  constructor
  · exact (div_pos hd ha).le
  · unfold groupBackwardF
    positivity

/-- Nonpositive backward coefficients reverse both input interval endpoints. -/
theorem backward_interval_nonpos (G Gnext D A F lo hi dlo dhi : ℝ)
    (he : G = A*Gnext-F*D) (hA : A ≤ 0) (hF : F ≤ 0)
    (hlo : lo ≤ Gnext) (hhi : Gnext ≤ hi) (hdlo : dlo ≤ D) (hdhi : D ≤ dhi) :
    A*hi-F*dlo ≤ G ∧ G ≤ A*lo-F*dhi := by
  rw [he]
  constructor
  · exact sub_le_sub (mul_le_mul_of_nonpos_left hhi hA)
      (mul_le_mul_of_nonpos_left hdlo hF)
  · exact sub_le_sub (mul_le_mul_of_nonpos_left hlo hA)
      (mul_le_mul_of_nonpos_left hdhi hF)

end KsIndex.PowerArc
