module

public import KsIndexLean.ProdValid
public import KsIndexLean.NegSignEndpointBridge

@[expose] public section

/-! Tail Mn: K = 16385, c = 49154, sign -1. -/
set_option maxHeartbeats 2000000
set_option linter.style.longLine false
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial PowerArc
def kMn : Fin 25 → ℤ := ![16379,16380,16381,16382,16383,16384,16386,16387,16388,16389,16390,16391,16379,16380,16381,16382,16383,16384,16385,16386,16387,16388,16389,16390,16391]
def kqMn : Fin 25 → ℚ := ![16379,16380,16381,16382,16383,16384,16386,16387,16388,16389,16390,16391,16379,16380,16381,16382,16383,16384,16385,16386,16387,16388,16389,16390,16391]
noncomputable def rMn : Fin 25 → ℝ := fun i => ((kMn i : ℤ) : ℝ)
def cenMn : Fin 25 → ℚ := ![(-21030661768186288298806384033976944234790349 / 2500000000000000000000000000000000000000000000 : ℚ),(-33953542089696253189497491049826143 / 5000000000000000000000000000000000000 : ℚ),(2102955149103181370297182679185168419724733 / 250000000000000000000000000000000000000000000 : ℚ),(339517496810161853984577827422351 / 50000000000000000000000000000000000 : ℚ),(-42056882816076907518370710855224822161165293 / 5000000000000000000000000000000000000000000000 : ℚ),(-33949957585766707963957526502788997 / 5000000000000000000000000000000000000 : ℚ),(33948165803854759792624625839491681 / 5000000000000000000000000000000000000 : ℚ),(-10513110912152246683734327217674291523496223 / 1250000000000000000000000000000000000000000000 : ℚ),(-33946374335187318776918170188366657 / 5000000000000000000000000000000000000 : ℚ),(4205022464689732212032762721894842161640613 / 500000000000000000000000000000000000000000000 : ℚ),(8486145794917850443510061380165651 / 1250000000000000000000000000000000000 : ℚ),(-42048006033046959320069975101676964304112417 / 5000000000000000000000000000000000000000000000 : ℚ),(-9730855964398346584216734827928052514165409 / 5000000000000000000000000000000000000000000000 : ℚ),(-12053755435241950301283356374635801 / 5000000000000000000000000000000000000 : ℚ),(1946036302736385965874917615540235265191781 / 1000000000000000000000000000000000000000000000 : ℚ),(6026460017075449194850348898522301 / 2500000000000000000000000000000000000 : ℚ),(-2432376798012243011967515237165552669884473 / 1250000000000000000000000000000000000000000000 : ℚ),(-12052084792937918289154996893963217 / 5000000000000000000000000000000000000 : ℚ),(1216104124932376654246811036535475753357449 / 625000000000000000000000000000000000000000000 : ℚ),(6025624855776450384187900151340089 / 2500000000000000000000000000000000000 : ℚ),(-9728158935871611000715747646016518678208903 / 5000000000000000000000000000000000000000000000 : ℚ),(-241008295798915168307585407598241 / 100000000000000000000000000000000000 : ℚ),(2431871250311585142514051358872000271966919 / 1250000000000000000000000000000000000000000000 : ℚ),(1204958002806642562530555748623609 / 500000000000000000000000000000000000 : ℚ),(-1945362239108558952615680645739739041511893 / 1000000000000000000000000000000000000000000000 : ℚ)]
def radMn : Fin 25 → ℚ := ![(87665544017582774670658349200064101 / 2500000000000000000000000000000000000000000000 : ℚ),(67077870521571 / 500000000000000000000000000000000000 : ℚ),(8766091586789216244629614193281737 / 250000000000000000000000000000000000000000000 : ℚ),(670942517377519 / 5000000000000000000000000000000000000 : ℚ),(175312577055110103652401654551779587 / 5000000000000000000000000000000000000000000000 : ℚ),(81922161809 / 610351562500000000000000000000000 : ℚ),(671270201701137 / 5000000000000000000000000000000000000 : ℚ),(10955879534247519064218695190133593 / 312500000000000000000000000000000000000000000 : ℚ),(335717036931473 / 2500000000000000000000000000000000000 : ℚ),(17528482272052404806441213911706163 / 500000000000000000000000000000000000000000000 : ℚ),(134319593204951 / 1000000000000000000000000000000000000 : ℚ),(175275574509873434935324499015359343 / 5000000000000000000000000000000000000000000000 : ℚ),(5269665533832714198456186271748937 / 1000000000000000000000000000000000000000000000 : ℚ),(67078424478429 / 500000000000000000000000000000000000 : ℚ),(329331268159900313598619593583241 / 62500000000000000000000000000000000000000000 : ℚ),(670948057622481 / 5000000000000000000000000000000000000 : ℚ),(26344675585940941332135967985168517 / 5000000000000000000000000000000000000000000000 : ℚ),(81922838191 / 610351562500000000000000000000000 : ℚ),(329285625856259572469543207676207 / 62500000000000000000000000000000000000000000 : ℚ),(671275743298863 / 5000000000000000000000000000000000000 : ℚ),(5268204980072398452636708895154937 / 1000000000000000000000000000000000000000000000 : ℚ),(335719808068527 / 2500000000000000000000000000000000000 : ℚ),(13169600040707581093940332569501927 / 2500000000000000000000000000000000000000000000 : ℚ),(134320701795049 / 1000000000000000000000000000000000000 : ℚ),(5267475122310172936767573514515843 / 1000000000000000000000000000000000000000000000 : ℚ)]
theorem heMn_0 : |tailEndpoint rMn 0 - ((cenMn 0 : ℚ) : ℝ)| ≤ ((radMn 0 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 0 (by decide)
    (A := -713622972037333227868746) (Z := 719689657) (E := 2140868916117893222231978)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMn, kMn, exponentQ]) (by norm_num [radMn, kMn, exponentQ])
theorem heMn_1 : |tailEndpoint rMn 1 - ((cenMn 1 : ℚ) : ℝ)| ≤ ((radMn 1 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 1 (by decide)
    (A := -414562220822420259999727) (Z := 1000000000) (E := 8190000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMn, kMn, exponentQ]) (by norm_num [radMn, kMn, exponentQ])
theorem heMn_2 : |tailEndpoint rMn 2 - ((cenMn 2 : ℚ) : ℝ)| ≤ ((radMn 2 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 2 (by decide)
    (A := 713498176322016862438820) (Z := 719689657) (E := 2140494528971944845631860)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMn, kMn, exponentQ]) (by norm_num [radMn, kMn, exponentQ])
theorem heMn_3 : |tailEndpoint rMn 3 - ((cenMn 3 : ℚ) : ℝ)| ≤ ((radMn 3 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 3 (by decide)
    (A := 414489728157629675023900) (Z := 1000000000) (E := 8191000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMn, kMn, exponentQ]) (by norm_num [radMn, kMn, exponentQ])
theorem heMn_4 : |tailEndpoint rMn 4 - ((cenMn 4 : ℚ) : ℝ)| ≤ ((radMn 4 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 4 (by decide)
    (A := -713373417662223910645061) (Z := 719689657) (E := 2140120252992566709940243)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMn, kMn, exponentQ]) (by norm_num [radMn, kMn, exponentQ])
theorem heMn_5 : |tailEndpoint rMn 5 - ((cenMn 5 : ℚ) : ℝ)| ≤ ((radMn 5 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 5 (by decide)
    (A := -414417257016732591287733) (Z := 1000000000) (E := 8192000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMn, kMn, exponentQ]) (by norm_num [radMn, kMn, exponentQ])
theorem heMn_6 : |tailEndpoint rMn 6 - ((cenMn 6 : ℚ) : ℝ)| ≤ ((radMn 6 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 6 (by decide)
    (A := 414344807390712062550609) (Z := 1000000000) (E := 8193000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMn, kMn, exponentQ]) (by norm_num [radMn, kMn, exponentQ])
theorem heMn_7 : |tailEndpoint rMn 7 - ((cenMn 7 : ℚ) : ℝ)| ≤ ((radMn 7 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 7 (by decide)
    (A := -713124011447118577206684) (Z := 719689657) (E := 2139372034347252149004432)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMn, kMn, exponentQ]) (by norm_num [radMn, kMn, exponentQ])
theorem heMn_8 : |tailEndpoint rMn 8 - ((cenMn 8 : ℚ) : ℝ)| ≤ ((radMn 8 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 8 (by decide)
    (A := -414272379270556019959473) (Z := 1000000000) (E := 8194000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMn, kMn, exponentQ]) (by norm_num [radMn, kMn, exponentQ])
theorem heMn_9 : |tailEndpoint rMn 9 - ((cenMn 9 : ℚ) : ℝ)| ≤ ((radMn 9 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 9 (by decide)
    (A := 712999363860782349447010) (Z := 719689657) (E := 2138998091588244185415070)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMn, kMn, exponentQ]) (by norm_num [radMn, kMn, exponentQ])
theorem heMn_10 : |tailEndpoint rMn 10 - ((cenMn 10 : ℚ) : ℝ)| ≤ ((radMn 10 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 10 (by decide)
    (A := 414199972647257268815756) (Z := 1000000000) (E := 8195000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMn, kMn, exponentQ]) (by norm_num [radMn, kMn, exponentQ])
theorem heMn_11 : |tailEndpoint rMn 11 - ((cenMn 11 : ℚ) : ℝ)| ≤ ((radMn 11 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 11 (by decide)
    (A := -712874753267921831963609) (Z := 719689657) (E := 2138624259809663352654527)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMn, kMn, exponentQ]) (by norm_num [radMn, kMn, exponentQ])
theorem heMn_12 : |tailEndpoint rMn 12 - ((cenMn 12 : ℚ) : ℝ)| ≤ ((radMn 12 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 12 (by decide)
    (A := -160860947313525647049469) (Z := 738631771) (E := 321721894633099949688035)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMn, kMn, exponentQ]) (by norm_num [radMn, kMn, exponentQ])
theorem heMn_13 : |tailEndpoint rMn 13 - ((cenMn 13 : ℚ) : ℝ)| ≤ ((radMn 13 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 13 (by decide)
    (A := -147171400912044253302711) (Z := 1000000000) (E := 8190000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMn, kMn, exponentQ]) (by norm_num [radMn, kMn, exponentQ])
theorem heMn_14 : |tailEndpoint rMn 14 - ((cenMn 14 : ℚ) : ℝ)| ≤ ((radMn 14 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 14 (by decide)
    (A := 160830160056595628511605) (Z := 738631771) (E := 321660320119240651244080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMn, kMn, exponentQ]) (by norm_num [radMn, kMn, exponentQ])
theorem heMn_15 : |tailEndpoint rMn 15 - ((cenMn 15 : ℚ) : ℝ)| ≤ ((radMn 15 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 15 (by decide)
    (A := 147143235423567431808422) (Z := 1000000000) (E := 8191000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMn, kMn, exponentQ]) (by norm_num [radMn, kMn, exponentQ])
theorem heMn_16 : |tailEndpoint rMn 16 - ((cenMn 16 : ℚ) : ℝ)| ≤ ((radMn 16 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 16 (by decide)
    (A := -160799382449644016681172) (Z := 738631771) (E := 321598764905338166214987)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMn, kMn, exponentQ]) (by norm_num [radMn, kMn, exponentQ])
theorem heMn_17 : |tailEndpoint rMn 17 - ((cenMn 17 : ℚ) : ℝ)| ≤ ((radMn 17 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 17 (by decide)
    (A := -147115078762761346786687) (Z := 1000000000) (E := 8192000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMn, kMn, exponentQ]) (by norm_num [radMn, kMn, exponentQ])
theorem heMn_18 : |tailEndpoint rMn 18 - ((cenMn 18 : ℚ) : ℝ)| ≤ ((radMn 18 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 18 (by decide)
    (A := 160768614488468621880872) (Z := 738631771) (E := 321537228982988115246160)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMn, kMn, exponentQ]) (by norm_num [radMn, kMn, exponentQ])
theorem heMn_19 : |tailEndpoint rMn 19 - ((cenMn 19 : ℚ) : ℝ)| ≤ ((radMn 19 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 19 (by decide)
    (A := 147086930925782126106158) (Z := 1000000000) (E := 8193000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMn, kMn, exponentQ]) (by norm_num [radMn, kMn, exponentQ])
theorem heMn_20 : |tailEndpoint rMn 20 - ((cenMn 20 : ℚ) : ℝ)| ≤ ((radMn 20 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 20 (by decide)
    (A := -160737856168869596950923) (Z := 738631771) (E := 321475712343790804018035)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMn, kMn, exponentQ]) (by norm_num [radMn, kMn, exponentQ])
theorem heMn_21 : |tailEndpoint rMn 21 - ((cenMn 21 : ℚ) : ℝ)| ≤ ((radMn 21 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 21 (by decide)
    (A := -147058791908788040277550) (Z := 1000000000) (E := 8194000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMn, kMn, exponentQ]) (by norm_num [radMn, kMn, exponentQ])
theorem heMn_22 : |tailEndpoint rMn 22 - ((cenMn 22 : ℚ) : ℝ)| ≤ ((radMn 22 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 22 (by decide)
    (A := 160707107486649435657516) (Z := 738631771) (E := 321414214979351220062994)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMn, kMn, exponentQ]) (by norm_num [radMn, kMn, exponentQ])
theorem heMn_23 : |tailEndpoint rMn 23 - ((cenMn 23 : ℚ) : ℝ)| ≤ ((radMn 23 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 23 (by decide)
    (A := 147030661707939500997990) (Z := 1000000000) (E := 8195000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMn, kMn, exponentQ]) (by norm_num [radMn, kMn, exponentQ])
theorem heMn_24 : |tailEndpoint rMn 24 - ((cenMn 24 : ℚ) : ℝ)| ≤ ((radMn 24 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 24 (by decide)
    (A := -160676368437612971102565) (Z := 738631771) (E := 321352736881279029584865)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenMn, kMn, exponentQ]) (by norm_num [radMn, kMn, exponentQ])
theorem heMn : ∀ i, |tailEndpoint rMn i - ((cenMn i : ℚ) : ℝ)| ≤ ((radMn i : ℚ) : ℝ) := by
  intro i
  fin_cases i
  · exact heMn_0
  · exact heMn_1
  · exact heMn_2
  · exact heMn_3
  · exact heMn_4
  · exact heMn_5
  · exact heMn_6
  · exact heMn_7
  · exact heMn_8
  · exact heMn_9
  · exact heMn_10
  · exact heMn_11
  · exact heMn_12
  · exact heMn_13
  · exact heMn_14
  · exact heMn_15
  · exact heMn_16
  · exact heMn_17
  · exact heMn_18
  · exact heMn_19
  · exact heMn_20
  · exact heMn_21
  · exact heMn_22
  · exact heMn_23
  · exact heMn_24
theorem leadMn : tailLeading rMn ≤ ((tailLeadingUpperQ cenMn radMn : ℚ) : ℝ) :=
  tailLeading_le_Q rMn cenMn radMn (by decide +kernel) heMn
theorem errMn : tailError rMn ((49154 : ℚ) : ℝ) ≤
    ((tailErrorUpperQ kqMn 49154 cenMn radMn : ℚ) : ℝ) :=
  tailError_le_Q rMn kqMn 49154 cenMn radMn
    (fun i => by fin_cases i <;> norm_num [rMn, kMn, kqMn])
    (by decide +kernel) (by decide +kernel) heMn
theorem leadValMn : tailLeadingUpperQ cenMn radMn = (1561382304903983020035649170484443971899076035705527133015437534831485297835653388486921409997473038282710539470022184369 / 245818383314062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by decide +kernel
theorem errValMn : tailErrorUpperQ kqMn 49154 cenMn radMn = (2414714989449614183908139581809693041638518918571056803833553843277334983035658615167519723681371230152121327219529986847723802107799314458477199852577293920169 / 58562793001762763482198157023827429718109911464753731250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by decide +kernel
end KsIndex.NegSignProd
