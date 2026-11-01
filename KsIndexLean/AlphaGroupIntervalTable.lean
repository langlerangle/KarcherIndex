module

public import KsIndexLean.AlphaGroupBackward

@[expose] public section


/-! Rational certificates for finite backward recurrence tables. -/
namespace KsIndex.PowerArc

/-- Outward containment of one backward interval step, including its sign. -/
def backwardStepOK (A F lo hi nextLo nextHi dlo dhi : ℚ) : Prop :=
  if 0 ≤ A ∧ 0 ≤ F then
    lo ≤ A*nextLo-F*dhi ∧ A*nextHi-F*dlo ≤ hi
  else if A ≤ 0 ∧ F ≤ 0 then
    lo ≤ A*nextHi-F*dlo ∧ A*nextLo-F*dhi ≤ hi
  else False

instance (A F lo hi nextLo nextHi dlo dhi : ℚ) :
    Decidable (backwardStepOK A F lo hi nextLo nextHi dlo dhi) := by
  unfold backwardStepOK
  infer_instance

/-- A checked rational row encloses the actual next-to-current recurrence. -/
theorem backwardStepOK_sound (A F lo hi nextLo nextHi dlo dhi : ℚ)
    (G Gnext D : ℝ)
    (he : G = (A:ℝ)*Gnext-(F:ℝ)*D)
    (hnext : (nextLo:ℝ) ≤ Gnext ∧ Gnext ≤ (nextHi:ℝ))
    (hD : (dlo:ℝ) ≤ D ∧ D ≤ (dhi:ℝ))
    (hcheck : backwardStepOK A F lo hi nextLo nextHi dlo dhi) :
    (lo:ℝ) ≤ G ∧ G ≤ (hi:ℝ) := by
  unfold backwardStepOK at hcheck
  split_ifs at hcheck with hp hn
  · have hh := backward_interval G Gnext D (A:ℝ) (F:ℝ)
      (nextLo:ℝ) (nextHi:ℝ) (dlo:ℝ) (dhi:ℝ) he
      (by exact_mod_cast hp.1) (by exact_mod_cast hp.2) hnext.1 hnext.2 hD.1 hD.2
    have hl : (lo:ℝ) ≤ (A:ℝ)*(nextLo:ℝ)-(F:ℝ)*(dhi:ℝ) := by exact_mod_cast hcheck.1
    have hu : (A:ℝ)*(nextHi:ℝ)-(F:ℝ)*(dlo:ℝ) ≤ (hi:ℝ) := by exact_mod_cast hcheck.2
    exact ⟨hl.trans hh.1, hh.2.trans hu⟩
  · have hh := backward_interval_nonpos G Gnext D (A:ℝ) (F:ℝ)
      (nextLo:ℝ) (nextHi:ℝ) (dlo:ℝ) (dhi:ℝ) he
      (by exact_mod_cast hn.1) (by exact_mod_cast hn.2) hnext.1 hnext.2 hD.1 hD.2
    have hl : (lo:ℝ) ≤ (A:ℝ)*(nextHi:ℝ)-(F:ℝ)*(dlo:ℝ) := by exact_mod_cast hcheck.1
    have hu : (A:ℝ)*(nextLo:ℝ)-(F:ℝ)*(dhi:ℝ) ≤ (hi:ℝ) := by exact_mod_cast hcheck.2
    exact ⟨hl.trans hh.1, hh.2.trans hu⟩

/-- Every entry of a checked finite table encloses the actual recurrence solution. -/
theorem backward_table_sound (L N : ℕ) (G : ℕ → ℝ) (D : ℝ)
    (A F lo hi : ℕ → ℚ) (dlo dhi : ℚ)
    (hD : (dlo:ℝ) ≤ D ∧ D ≤ (dhi:ℝ))
    (hanchor : (lo N:ℝ) ≤ G N ∧ G N ≤ (hi N:ℝ))
    (hrec : ∀ n, L ≤ n → n < N → G n = (A n:ℝ)*G (n+1)-(F n:ℝ)*D)
    (hcheck : ∀ n, L ≤ n → n < N →
      backwardStepOK (A n) (F n) (lo n) (hi n) (lo (n+1)) (hi (n+1)) dlo dhi)
    (n : ℕ) (hLn : L ≤ n) (hnN : n ≤ N) :
    (lo n:ℝ) ≤ G n ∧ G n ≤ (hi n:ℝ) := by
  exact Nat.decreasingInduction' (P := fun j => (lo j:ℝ) ≤ G j ∧ G j ≤ (hi j:ℝ))
    (fun k hk hnk ih => backwardStepOK_sound _ _ _ _ _ _ _ _ _ _ _
      (hrec k (hLn.trans hnk) hk) ih hD (hcheck k (hLn.trans hnk) hk)) hnN hanchor

/-- Rational forms of the analytic backward coefficients. -/
def groupBackwardAq (β r : ℚ) (n : ℕ) : ℚ :=
  ((n:ℚ)+9/2+1-(r-β)/2) / ((n:ℚ)+9/2+1-(r+β+2)/2)

def groupBackwardFq (β r : ℚ) (n : ℕ) : ℚ :=
  (r*((n:ℚ)+9/2)+(r+β)/2) /
    (((n:ℚ)+9/2)^2*((n:ℚ)+9/2+1)^2*((n:ℚ)+9/2+1-(r+β+2)/2))

@[simp] theorem groupBackwardAq_cast (β r : ℚ) (n : ℕ) :
    (groupBackwardAq β r n : ℝ) = groupBackwardA β r n := by
  simp [groupBackwardAq, groupBackwardA]

@[simp] theorem groupBackwardFq_cast (β r : ℚ) (n : ℕ) :
    (groupBackwardFq β r n : ℝ) = groupBackwardF β r n := by
  simp [groupBackwardFq, groupBackwardF]

/-- A rational table checked against the analytic coefficients encloses the
actual compensated group, including the sign-changing step at mode three. -/
theorem compensatedGroup_table_sound (β r : ℚ) (κ w : ℝ)
    (hβ : (0:ℚ) < β) (hβ1 : β < 1) (hr : r = 14 ∨ r = 15)
    (lo hi : ℕ → ℚ) (dlo dhi : ℚ)
    (hD : (dlo:ℝ) ≤ stieltjesCorrectionD β r κ ∧ stieltjesCorrectionD β r κ ≤ (dhi:ℝ))
    (hanchor : (lo 1024:ℝ) ≤ compensatedPowerArcGroup β r κ w 1024 ∧
      compensatedPowerArcGroup β r κ w 1024 ≤ (hi 1024:ℝ))
    (hcheck : ∀ n, 3 ≤ n → n < 1024 →
      backwardStepOK (groupBackwardAq β r n) (groupBackwardFq β r n)
        (lo n) (hi n) (lo (n+1)) (hi (n+1)) dlo dhi)
    (n : ℕ) (hn : 3 ≤ n) (hnN : n ≤ 1024) :
    (lo n:ℝ) ≤ compensatedPowerArcGroup β r κ w n ∧
      compensatedPowerArcGroup β r κ w n ≤ (hi n:ℝ) := by
  apply backward_table_sound 3 1024 (compensatedPowerArcGroup β r κ w)
    (stieltjesCorrectionD β r κ) (groupBackwardAq β r) (groupBackwardFq β r)
    lo hi dlo dhi hD hanchor ?_ hcheck n hn hnN
  intro j hj _
  have hb : (0:ℝ) < β := by exact_mod_cast hβ
  have hb1 : (β:ℝ) < 1 := by exact_mod_cast hβ1
  have hjR : (3:ℝ) ≤ j := by exact_mod_cast hj
  rw [groupBackwardAq_cast, groupBackwardFq_cast]
  apply compensatedPowerArcGroup_backward _ _ _ _ _ hb hb1
  · rcases hr with rfl | rfl <;> norm_num <;> linarith
  · rcases hr with rfl | rfl <;> norm_num <;> linarith
  · rcases hr with rfl | rfl <;> norm_num
    · linarith
    · by_cases h3 : j = 3
      · subst j; norm_num; linarith
      · have hj4 : (4:ℝ) ≤ j := by exact_mod_cast (show 4 ≤ j by omega)
        linarith

end KsIndex.PowerArc
