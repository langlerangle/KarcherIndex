module

public import KsIndexLean.AlphaMiddleGroupEnclosure
public import KsIndexLean.AlphaGroupForwardAnchor
public import KsIndexLean.AlphaGroupTableB15
public import KsIndexLean.AlphaGroupTableB14
public import KsIndexLean.AlphaGroupTableC15
public import KsIndexLean.AlphaGroupTableC14

@[expose] public section


/-! Certified compensated-group inputs on the whole middle window.
Mode 1025 uses its forward anchor, never an out-of-domain backward-table lookup. -/
namespace KsIndex.AlphaRemarkTrial.MiddleInterval
open PowerArc

def anchorLo : Fin 4 → ℚ := ![-441807651372963241849577/40000000000000000000000000000, -16649393537180759041457/1000000000000000000000000000000, 14809468441939931196431/1000000000000000000000000000000, 2091570950631087256342341/500000000000000000000000000000]
def tableLo (n : ℕ) : Fin 4 → ℚ := ![GroupTableB15.lo n, GroupTableB14.lo n, GroupTableC15.lo n, GroupTableC14.lo n]
def certifiedGroupLo (n : ℕ) (j : Fin 4) : ℚ :=
  if n = 1025 then anchorLo j else tableLo n j

def anchorHi : Fin 4 → ℚ := ![-2761242898148566208524661/250000000000000000000000000000, -4107425414176722587793/250000000000000000000000000000, 3757282770018199080363/250000000000000000000000000000, 2091680782032588442786441/500000000000000000000000000000]
def tableHi (n : ℕ) : Fin 4 → ℚ := ![GroupTableB15.hi n, GroupTableB14.hi n, GroupTableC15.hi n, GroupTableC14.hi n]
def certifiedGroupHi (n : ℕ) (j : Fin 4) : ℚ :=
  if n = 1025 then anchorHi j else tableHi n j

theorem certifiedGroup_encloses (n : ℕ) (hn : 3 ≤ n) (hN : n ≤ 1025) (j : Fin 4) :
    (certifiedGroupLo n j : ℝ) ≤ groupValue AlphaRemark.spectralUpper n j ∧
      groupValue AlphaRemark.spectralUpper n j ≤ (certifiedGroupHi n j : ℝ) := by
  by_cases hlast : n = 1025
  · subst n
    fin_cases j
    · convert forwardAnchor_b15 using 1 <;> norm_num [certifiedGroupLo, certifiedGroupHi, anchorLo, anchorHi, groupValue, groupBeta, groupEndpoint, AlphaRemark.spectralUpper]
    · convert forwardAnchor_b14 using 1 <;> norm_num [certifiedGroupLo, certifiedGroupHi, anchorLo, anchorHi, groupValue, groupBeta, groupEndpoint, AlphaRemark.spectralUpper]
    · convert forwardAnchor_c15 using 1 <;> norm_num [certifiedGroupLo, certifiedGroupHi, anchorLo, anchorHi, groupValue, groupBeta, groupEndpoint, AlphaRemark.spectralUpper]
    · convert forwardAnchor_c14 using 1 <;> norm_num [certifiedGroupLo, certifiedGroupHi, anchorLo, anchorHi, groupValue, groupBeta, groupEndpoint, AlphaRemark.spectralUpper]
  · have hN' : n ≤ 1024 := by omega
    fin_cases j
    · convert GroupTableB15.encloses n hn hN' using 1 <;> norm_num [certifiedGroupLo, certifiedGroupHi, hlast, tableLo, tableHi, groupValue, groupBeta, groupEndpoint, AlphaRemark.spectralUpper]
    · convert GroupTableB14.encloses n hn hN' using 1 <;> norm_num [certifiedGroupLo, certifiedGroupHi, hlast, tableLo, tableHi, groupValue, groupBeta, groupEndpoint, AlphaRemark.spectralUpper]
    · convert GroupTableC15.encloses n hn hN' using 1 <;> norm_num [certifiedGroupLo, certifiedGroupHi, hlast, tableLo, tableHi, groupValue, groupBeta, groupEndpoint, AlphaRemark.spectralUpper]
    · convert GroupTableC14.encloses n hn hN' using 1 <;> norm_num [certifiedGroupLo, certifiedGroupHi, hlast, tableLo, tableHi, groupValue, groupBeta, groupEndpoint, AlphaRemark.spectralUpper]

theorem certifiedAllGroups_encloses (n : ℕ) (hn : 3 ≤ n) (hN : n ≤ 1025) :
    (groupSumLo (groupMultiplier n) (certifiedGroupLo n) (certifiedGroupHi n) : ℝ) ≤
        allCompensatedGroups (2*AlphaRemark.spectralUpper^2/Real.pi) (1+AlphaRemark.spectralUpper^2) n ∧
      allCompensatedGroups (2*AlphaRemark.spectralUpper^2/Real.pi) (1+AlphaRemark.spectralUpper^2) n ≤
        (groupSumHi (groupMultiplier n) (certifiedGroupLo n) (certifiedGroupHi n) : ℝ) :=
  allGroups_enclosed _ _ _ _ (certifiedGroup_encloses n hn hN)

theorem certifiedAllGroupsR_encloses (n : ℕ) (hn : 3 ≤ n) (hN : n ≤ 1025) :
    (groupSumLo (groupMultiplierR n) (certifiedGroupLo n) (certifiedGroupHi n) : ℝ) ≤
        allCompensatedGroupsR (2*AlphaRemark.spectralUpper^2/Real.pi) (1+AlphaRemark.spectralUpper^2) n ∧
      allCompensatedGroupsR (2*AlphaRemark.spectralUpper^2/Real.pi) (1+AlphaRemark.spectralUpper^2) n ≤
        (groupSumHi (groupMultiplierR n) (certifiedGroupLo n) (certifiedGroupHi n) : ℝ) :=
  allGroupsR_enclosed _ _ _ _ (certifiedGroup_encloses n hn hN)

end KsIndex.AlphaRemarkTrial.MiddleInterval
#print axioms KsIndex.AlphaRemarkTrial.MiddleInterval.certifiedAllGroups_encloses
#print axioms KsIndex.AlphaRemarkTrial.MiddleInterval.certifiedAllGroupsR_encloses
