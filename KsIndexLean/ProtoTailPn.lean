module

public import KsIndexLean.ProtoValid
public import KsIndexLean.NegSignEndpointBridge

@[expose] public section

/-! Tail Pn: K = 130, c = 389, sign -1. -/
set_option maxHeartbeats 2000000
set_option linter.style.longLine false
namespace KsIndex.NegSignProto
open KsIndex.AlphaRemarkTrial PowerArc
def kPn : Fin 25 → ℤ := ![124,125,126,127,128,129,131,132,133,134,135,136,124,125,126,127,128,129,130,131,132,133,134,135,136]
def kqPn : Fin 25 → ℚ := ![124,125,126,127,128,129,131,132,133,134,135,136,124,125,126,127,128,129,130,131,132,133,134,135,136]
noncomputable def rPn : Fin 25 → ℝ := fun i => ((kPn i : ℤ) : ℝ)
def cenPn : Fin 25 → ℚ := ![(-140719781693533013559856553603914869 / 2500000000000000000000000000000000000 : ℚ),(86854262008187942699123371545550743564989709 / 1250000000000000000000000000000000000000000000 : ℚ),(139741871168835040944469549212168741 / 2500000000000000000000000000000000000 : ℚ),(-172510987287555978775275386890301250271406723 / 2500000000000000000000000000000000000000000000 : ℚ),(-138786118288895948923081326751443057 / 2500000000000000000000000000000000000 : ℚ),(342680743197779835606498729419955353437541367 / 5000000000000000000000000000000000000000000000 : ℚ),(-170195665121360973834566179698293876051307611 / 2500000000000000000000000000000000000000000000 : ℚ),(-136937772511820895480946444402761813 / 2500000000000000000000000000000000000 : ℚ),(338151817747738574431237278387522946865718687 / 5000000000000000000000000000000000000000000000 : ℚ),(272087261223323690657568213438714291 / 5000000000000000000000000000000000000 : ℚ),(-13438415456977857736872955310232205689013527 / 200000000000000000000000000000000000000000000 : ℚ),(-270337085351317454241429471327116309 / 5000000000000000000000000000000000000 : ℚ),(-48410667674137173255651537965349899 / 1250000000000000000000000000000000000 : ℚ),(19450402001916598056900440855517233071037409 / 625000000000000000000000000000000000000000000 : ℚ),(95938931389865013465766496474542107 / 2500000000000000000000000000000000000 : ℚ),(-3854909582997843504619508951854294300223897 / 125000000000000000000000000000000000000000000 : ℚ),(-95078385943990264189032604801204461 / 2500000000000000000000000000000000000 : ℚ),(152824126865075245579276931717033786693706829 / 5000000000000000000000000000000000000000000000 : ℚ),(301564242986293933661185017364523 / 8000000000000000000000000000000000 : ℚ),(-30297015251613104921845438844171080094673339 / 1000000000000000000000000000000000000000000000 : ℚ),(-93419425992154819567063713500665771 / 2500000000000000000000000000000000000 : ℚ),(150177935426316656902164600576899490756308617 / 5000000000000000000000000000000000000000000000 : ℚ),(92619405179606014938810589086770481 / 2500000000000000000000000000000000000 : ℚ),(-37225369383590337281703034641411048821494671 / 1250000000000000000000000000000000000000000000 : ℚ),(-91838023962777580849089907126485061 / 2500000000000000000000000000000000000 : ℚ)]
def radPn : Fin 25 → ℚ := ![(19287016079 / 2500000000000000000000000000000000000 : ℚ),(362048812971288585758288006312061281 / 1250000000000000000000000000000000000000000000 : ℚ),(39826193967 / 5000000000000000000000000000000000000 : ℚ),(719105737909288790461881246048468627 / 2500000000000000000000000000000000000000000000 : ℚ),(642161809 / 78125000000000000000000000000000000 : ℚ),(1428452138493550044546862634302874253 / 5000000000000000000000000000000000000000000000 : ℚ),(709454402182804931662395903677180119 / 2500000000000000000000000000000000000000000000 : ℚ),(21851339697 / 2500000000000000000000000000000000000 : ℚ),(1409573478479510434454637761021668413 / 5000000000000000000000000000000000000000000000 : ℚ),(45034841203 / 5000000000000000000000000000000000000 : ℚ),(280087715439639659505326554767945861 / 1000000000000000000000000000000000000000000000 : ℚ),(11596750753 / 1250000000000000000000000000000000000 : ℚ),(19307983921 / 2500000000000000000000000000000000000 : ℚ),(42132825075928881232420708928868513 / 500000000000000000000000000000000000000000000 : ℚ),(39868806033 / 5000000000000000000000000000000000000 : ℚ),(417518957006558958716814829722607069 / 5000000000000000000000000000000000000000000000 : ℚ),(642838191 / 78125000000000000000000000000000000 : ℚ),(8276065713131923045294215065652847 / 100000000000000000000000000000000000000000000 : ℚ),(8486896483 / 1000000000000000000000000000000000000 : ℚ),(82035505216883250625037091575853177 / 1000000000000000000000000000000000000000000000 : ℚ),(21873660303 / 2500000000000000000000000000000000000 : ℚ),(101659542225619123094793366263931023 / 1250000000000000000000000000000000000000000000 : ℚ),(45080158797 / 5000000000000000000000000000000000000 : ℚ),(403181892197164536848883503714576289 / 5000000000000000000000000000000000000000000000 : ℚ),(11608249247 / 1250000000000000000000000000000000000 : ℚ)]
theorem hePn_0 : |tailEndpoint rPn 0 - ((cenPn 0 : ℚ) : ℝ)| ≤ ((radPn 0 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 0 (by decide)
    (A := -452357504616722668555364682) (Z := 1000000000) (E := 62000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePn_1 : |tailEndpoint rPn 1 - ((cenPn 1 : ℚ) : ℝ)| ≤ ((radPn 1 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 1 (by decide)
    (A := 769708460720995164555540372) (Z := 719689657) (E := 2309125382162985538287380036)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePn_2 : |tailEndpoint rPn 2 - ((cenPn 2 : ℚ) : ℝ)| ≤ ((radPn 2 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 2 (by decide)
    (A := 442107919774176174392937898) (Z := 1000000000) (E := 63000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePn_3 : |tailEndpoint rPn 3 - ((cenPn 3 : ℚ) : ℝ)| ≤ ((radPn 3 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 3 (by decide)
    (A := -752405148113419308864320342) (Z := 719689657) (E := 2257215444340257971933409606)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePn_4 : |tailEndpoint rPn 4 - ((cenPn 4 : ℚ) : ℝ)| ≤ ((radPn 4 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 4 (by decide)
    (A := -432246565721556165988318146) (Z := 1000000000) (E := 64000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePn_5 : |tailEndpoint rPn 5 - ((cenPn 5 : ℚ) : ℝ)| ≤ ((radPn 5 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 5 (by decide)
    (A := 735752181617353965716117759) (Z := 719689657) (E := 2207256544852061943208491517)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePn_6 : |tailEndpoint rPn 6 - ((cenPn 6 : ℚ) : ℝ)| ≤ ((radPn 6 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 6 (by decide)
    (A := -719715593599267235457417094) (Z := 719689657) (E := 2159146780797801753152079182)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePn_7 : |tailEndpoint rPn 7 - ((cenPn 7 : ℚ) : ℝ)| ≤ ((radPn 7 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 7 (by decide)
    (A := -413608186550731425469288714) (Z := 1000000000) (E := 66000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePn_8 : |tailEndpoint rPn 8 - ((cenPn 8 : ℚ) : ℝ)| ≤ ((radPn 8 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 8 (by decide)
    (A := 704263673102182623468471399) (Z := 719689657) (E := 2112791019306547917904931757)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePn_9 : |tailEndpoint rPn 9 - ((cenPn 9 : ℚ) : ℝ)| ≤ ((radPn 9 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 9 (by decide)
    (A := 404794288488538167835072899) (Z := 1000000000) (E := 67000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePn_10 : |tailEndpoint rPn 10 - ((cenPn 10 : ℚ) : ℝ)| ≤ ((radPn 10 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 10 (by decide)
    (A := -689366784809428152926851975) (Z := 719689657) (E := 2068100354428284506999763145)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePn_11 : |tailEndpoint rPn 11 - ((cenPn 11 : ℚ) : ℝ)| ≤ ((radPn 11 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 11 (by decide)
    (A := -396294664674371200750450501) (Z := 1000000000) (E := 68000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePn_12 : |tailEndpoint rPn 12 - ((cenPn 12 : ℚ) : ℝ)| ≤ ((radPn 12 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 12 (by decide)
    (A := -310903656029257032221079956) (Z := 1000000000) (E := 62000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePn_13 : |tailEndpoint rPn 13 - ((cenPn 13 : ℚ) : ℝ)| ≤ ((radPn 13 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 13 (by decide)
    (A := 335538883106339085043211752) (Z := 738631771) (E := 671077766212678215881593430)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePn_14 : |tailEndpoint rPn 14 - ((cenPn 14 : ℚ) : ℝ)| ≤ ((radPn 14 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 14 (by decide)
    (A := 303202091006119488340950954) (Z := 1000000000) (E := 63000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePn_15 : |tailEndpoint rPn 15 - ((cenPn 15 : ℚ) : ℝ)| ≤ ((radPn 15 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 15 (by decide)
    (A := -327292221520927185305355080) (Z := 738631771) (E := 654584443041854417144511859)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePn_16 : |tailEndpoint rPn 16 - ((cenPn 16 : ℚ) : ℝ)| ≤ ((radPn 16 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 16 (by decide)
    (A := -295808143558136122590863942) (Z := 1000000000) (E := 64000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePn_17 : |tailEndpoint rPn 17 - ((cenPn 17 : ℚ) : ℝ)| ≤ ((radPn 17 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 17 (by decide)
    (A := 319372407651555171775773689) (Z := 738631771) (E := 638744815303110390823980850)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePn_18 : |tailEndpoint rPn 18 - ((cenPn 18 : ℚ) : ℝ)| ≤ ((radPn 18 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 18 (by decide)
    (A := 288705002962110267440283125) (Z := 1000000000) (E := 65000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePn_19 : |tailEndpoint rPn 19 - ((cenPn 19 : ℚ) : ℝ)| ≤ ((radPn 19 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 19 (by decide)
    (A := -311761715643852168459517995) (Z := 738631771) (E := 623523431287704384930101235)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePn_20 : |tailEndpoint rPn 20 - ((cenPn 20 : ℚ) : ℝ)| ≤ ((radPn 20 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 20 (by decide)
    (A := -281877016926910355311930762) (Z := 1000000000) (E := 66000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePn_21 : |tailEndpoint rPn 21 - ((cenPn 21 : ℚ) : ℝ)| ≤ ((radPn 21 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 21 (by decide)
    (A := 304443631992346226739123397) (Z := 738631771) (E := 608887263984692502227943812)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePn_22 : |tailEndpoint rPn 22 - ((cenPn 22 : ℚ) : ℝ)| ≤ ((radPn 22 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 22 (by decide)
    (A := 275309595734900889235672382) (Z := 1000000000) (E := 67000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePn_23 : |tailEndpoint rPn 23 - ((cenPn 23 : ℚ) : ℝ)| ≤ ((radPn 23 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 23 (by decide)
    (A := -297402755960356107541751244) (Z := 738631771) (E := 594805511920712264571831279)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePn_24 : |tailEndpoint rPn 24 - ((cenPn 24 : ℚ) : ℝ)| ≤ ((radPn 24 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 24 (by decide)
    (A := -268989125603191637677717142) (Z := 1000000000) (E := 68000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem hePn : ∀ i, |tailEndpoint rPn i - ((cenPn i : ℚ) : ℝ)| ≤ ((radPn i : ℚ) : ℝ) := by
  intro i
  fin_cases i
  · exact hePn_0
  · exact hePn_1
  · exact hePn_2
  · exact hePn_3
  · exact hePn_4
  · exact hePn_5
  · exact hePn_6
  · exact hePn_7
  · exact hePn_8
  · exact hePn_9
  · exact hePn_10
  · exact hePn_11
  · exact hePn_12
  · exact hePn_13
  · exact hePn_14
  · exact hePn_15
  · exact hePn_16
  · exact hePn_17
  · exact hePn_18
  · exact hePn_19
  · exact hePn_20
  · exact hePn_21
  · exact hePn_22
  · exact hePn_23
  · exact hePn_24
theorem leadPn : tailLeading rPn ≤ ((tailLeadingUpperQ cenPn radPn : ℚ) : ℝ) :=
  tailLeading_le_Q rPn cenPn radPn (by decide +kernel) hePn
theorem errPn : tailError rPn ((389 : ℚ) : ℝ) ≤
    ((tailErrorUpperQ kqPn 389 cenPn radPn : ℚ) : ℝ) :=
  tailError_le_Q rPn kqPn 389 cenPn radPn
    (fun i => by fin_cases i <;> norm_num [rPn, kPn, kqPn])
    (by decide +kernel) (by decide +kernel) hePn
theorem leadValPn : tailLeadingUpperQ cenPn radPn = (167214155361131958609573173500305833392408140201037861660699579197725133421725585608753131390621582900583250743765329381695611 / 25565111864662500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by decide +kernel
theorem errValPn : tailErrorUpperQ kqPn 389 cenPn radPn = (618447222747314762648752816690257499519805723929288590378085595279549840060780998103864512296779513024176083667561358672431362185412235067 / 787298941563250433192719593750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by decide +kernel
end KsIndex.NegSignProto
