module

public import KsIndexLean.ProdValid
public import KsIndexLean.NegSignEndpointBridge

@[expose] public section

/-! Tail Pn: K = 16386, c = 49157, sign -1. -/
set_option maxHeartbeats 2000000
set_option linter.style.longLine false
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial PowerArc
def kPn : Fin 25 → ℤ := ![16380,16381,16382,16383,16384,16385,16387,16388,16389,16390,16391,16392,16380,16381,16382,16383,16384,16385,16386,16387,16388,16389,16390,16391,16392]
def kqPn : Fin 25 → ℚ := ![16380,16381,16382,16383,16384,16385,16387,16388,16389,16390,16391,16392,16380,16381,16382,16383,16384,16385,16386,16387,16388,16389,16390,16391,16392]
noncomputable def rPn : Fin 25 → ℝ := fun i => ((kPn i : ℤ) : ℝ)
def cenPn : Fin 25 → ℚ := ![(-33953542089696253189497491049826143 / 5000000000000000000000000000000000000 : ℚ),(2102955149103181370297182679185168419724733 / 250000000000000000000000000000000000000000000 : ℚ),(339517496810161853984577827422351 / 50000000000000000000000000000000000 : ℚ),(-42056882816076907518370710855224822161165293 / 5000000000000000000000000000000000000000000000 : ℚ),(-33949957585766707963957526502788997 / 5000000000000000000000000000000000000 : ℚ),(21027331519148556313991420253931099021519477 / 2500000000000000000000000000000000000000000000 : ℚ),(-10513110912152246683734327217674291523496223 / 1250000000000000000000000000000000000000000000 : ℚ),(-33946374335187318776918170188366657 / 5000000000000000000000000000000000000 : ℚ),(4205022464689732212032762721894842161640613 / 500000000000000000000000000000000000000000000 : ℚ),(8486145794917850443510061380165651 / 1250000000000000000000000000000000000 : ℚ),(-42048006033046959320069975101676964304112417 / 5000000000000000000000000000000000000000000000 : ℚ),(-16971396168607032292431095083769589 / 2500000000000000000000000000000000000 : ℚ),(-12053755435241950301283356374635801 / 5000000000000000000000000000000000000 : ℚ),(1946036302736385965874917615540235265191781 / 1000000000000000000000000000000000000000000000 : ℚ),(6026460017075449194850348898522301 / 2500000000000000000000000000000000000 : ℚ),(-2432376798012243011967515237165552669884473 / 1250000000000000000000000000000000000000000000 : ℚ),(-12052084792937918289154996893963217 / 5000000000000000000000000000000000000 : ℚ),(1216104124932376654246811036535475753357449 / 625000000000000000000000000000000000000000000 : ℚ),(6025624855776450384187900151340089 / 2500000000000000000000000000000000000 : ℚ),(-9728158935871611000715747646016518678208903 / 5000000000000000000000000000000000000000000000 : ℚ),(-241008295798915168307585407598241 / 100000000000000000000000000000000000 : ℚ),(2431871250311585142514051358872000271966919 / 1250000000000000000000000000000000000000000000 : ℚ),(1204958002806642562530555748623609 / 500000000000000000000000000000000000 : ℚ),(-1945362239108558952615680645739739041511893 / 1000000000000000000000000000000000000000000000 : ℚ),(-602437271293242929413252879127957 / 250000000000000000000000000000000000 : ℚ)]
def radPn : Fin 25 → ℚ := ![(67077870521571 / 500000000000000000000000000000000000 : ℚ),(8766091586789216244629614193281737 / 250000000000000000000000000000000000000000000 : ℚ),(670942517377519 / 5000000000000000000000000000000000000 : ℚ),(175312577055110103652401654551779587 / 5000000000000000000000000000000000000000000000 : ℚ),(81922161809 / 610351562500000000000000000000000 : ℚ),(87651661996331121918326225577176023 / 2500000000000000000000000000000000000000000000 : ℚ),(10955879534247519064218695190133593 / 312500000000000000000000000000000000000000000 : ℚ),(335717036931473 / 2500000000000000000000000000000000000 : ℚ),(17528482272052404806441213911706163 / 500000000000000000000000000000000000000000000 : ℚ),(134319593204951 / 1000000000000000000000000000000000000 : ℚ),(175275574509873434935324499015359343 / 5000000000000000000000000000000000000000000000 : ℚ),(167940469546641 / 1250000000000000000000000000000000000 : ℚ),(67078424478429 / 500000000000000000000000000000000000 : ℚ),(329331268159900313598619593583241 / 62500000000000000000000000000000000000000000 : ℚ),(670948057622481 / 5000000000000000000000000000000000000 : ℚ),(26344675585940941332135967985168517 / 5000000000000000000000000000000000000000000000 : ℚ),(81922838191 / 610351562500000000000000000000000 : ℚ),(329285625856259572469543207676207 / 62500000000000000000000000000000000000000000 : ℚ),(671275743298863 / 5000000000000000000000000000000000000 : ℚ),(5268204980072398452636708895154937 / 1000000000000000000000000000000000000000000000 : ℚ),(335719808068527 / 2500000000000000000000000000000000000 : ℚ),(13169600040707581093940332569501927 / 2500000000000000000000000000000000000000000000 : ℚ),(134320701795049 / 1000000000000000000000000000000000000 : ℚ),(5267475122310172936767573514515843 / 1000000000000000000000000000000000000000000000 : ℚ),(167941855453359 / 1250000000000000000000000000000000000 : ℚ)]
theorem hePn_0 : |tailEndpoint rPn 0 - ((cenPn 0 : ℚ) : ℝ)| ≤ ((radPn 0 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 0 (by decide)
    (A := -414562220822420259999727) (Z := 1000000000) (E := 8190000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPn, kPn, exponentQ]) (by norm_num [radPn, kPn, exponentQ])
theorem hePn_1 : |tailEndpoint rPn 1 - ((cenPn 1 : ℚ) : ℝ)| ≤ ((radPn 1 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 1 (by decide)
    (A := 713498176322016862438820) (Z := 719689657) (E := 2140494528971944845631860)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPn, kPn, exponentQ]) (by norm_num [radPn, kPn, exponentQ])
theorem hePn_2 : |tailEndpoint rPn 2 - ((cenPn 2 : ℚ) : ℝ)| ≤ ((radPn 2 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 2 (by decide)
    (A := 414489728157629675023900) (Z := 1000000000) (E := 8191000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPn, kPn, exponentQ]) (by norm_num [radPn, kPn, exponentQ])
theorem hePn_3 : |tailEndpoint rPn 3 - ((cenPn 3 : ℚ) : ℝ)| ≤ ((radPn 3 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 3 (by decide)
    (A := -713373417662223910645061) (Z := 719689657) (E := 2140120252992566709940243)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPn, kPn, exponentQ]) (by norm_num [radPn, kPn, exponentQ])
theorem hePn_4 : |tailEndpoint rPn 4 - ((cenPn 4 : ℚ) : ℝ)| ≤ ((radPn 4 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 4 (by decide)
    (A := -414417257016732591287733) (Z := 1000000000) (E := 8192000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPn, kPn, exponentQ]) (by norm_num [radPn, kPn, exponentQ])
theorem hePn_5 : |tailEndpoint rPn 5 - ((cenPn 5 : ℚ) : ℝ)| ≤ ((radPn 5 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 5 (by decide)
    (A := 713248696042429855314458) (Z := 719689657) (E := 2139746088133185263638094)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPn, kPn, exponentQ]) (by norm_num [radPn, kPn, exponentQ])
theorem hePn_6 : |tailEndpoint rPn 6 - ((cenPn 6 : ℚ) : ℝ)| ≤ ((radPn 6 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 6 (by decide)
    (A := -713124011447118577206684) (Z := 719689657) (E := 2139372034347252149004432)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPn, kPn, exponentQ]) (by norm_num [radPn, kPn, exponentQ])
theorem hePn_7 : |tailEndpoint rPn 7 - ((cenPn 7 : ℚ) : ℝ)| ≤ ((radPn 7 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 7 (by decide)
    (A := -414272379270556019959473) (Z := 1000000000) (E := 8194000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPn, kPn, exponentQ]) (by norm_num [radPn, kPn, exponentQ])
theorem hePn_8 : |tailEndpoint rPn 8 - ((cenPn 8 : ℚ) : ℝ)| ≤ ((radPn 8 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 8 (by decide)
    (A := 712999363860782349447010) (Z := 719689657) (E := 2138998091588244185415070)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPn, kPn, exponentQ]) (by norm_num [radPn, kPn, exponentQ])
theorem hePn_9 : |tailEndpoint rPn 9 - ((cenPn 9 : ℚ) : ℝ)| ≤ ((radPn 9 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 9 (by decide)
    (A := 414199972647257268815756) (Z := 1000000000) (E := 8195000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPn, kPn, exponentQ]) (by norm_num [radPn, kPn, exponentQ])
theorem hePn_10 : |tailEndpoint rPn 10 - ((cenPn 10 : ℚ) : ℝ)| ≤ ((radPn 10 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 10 (by decide)
    (A := -712874753267921831963609) (Z := 719689657) (E := 2138624259809663352654527)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPn, kPn, exponentQ]) (by norm_num [radPn, kPn, exponentQ])
theorem hePn_11 : |tailEndpoint rPn 11 - ((cenPn 11 : ℚ) : ℝ)| ≤ ((radPn 11 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 11 (by decide)
    (A := -414127587511813485344842) (Z := 1000000000) (E := 8196000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPn, kPn, exponentQ]) (by norm_num [radPn, kPn, exponentQ])
theorem hePn_12 : |tailEndpoint rPn 12 - ((cenPn 12 : ℚ) : ℝ)| ≤ ((radPn 12 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 12 (by decide)
    (A := -147171400912044253302711) (Z := 1000000000) (E := 8190000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPn, kPn, exponentQ]) (by norm_num [radPn, kPn, exponentQ])
theorem hePn_13 : |tailEndpoint rPn 13 - ((cenPn 13 : ℚ) : ℝ)| ≤ ((radPn 13 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 13 (by decide)
    (A := 160830160056595628511605) (Z := 738631771) (E := 321660320119240651244080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPn, kPn, exponentQ]) (by norm_num [radPn, kPn, exponentQ])
theorem hePn_14 : |tailEndpoint rPn 14 - ((cenPn 14 : ℚ) : ℝ)| ≤ ((radPn 14 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 14 (by decide)
    (A := 147143235423567431808422) (Z := 1000000000) (E := 8191000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPn, kPn, exponentQ]) (by norm_num [radPn, kPn, exponentQ])
theorem hePn_15 : |tailEndpoint rPn 15 - ((cenPn 15 : ℚ) : ℝ)| ≤ ((radPn 15 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 15 (by decide)
    (A := -160799382449644016681172) (Z := 738631771) (E := 321598764905338166214987)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPn, kPn, exponentQ]) (by norm_num [radPn, kPn, exponentQ])
theorem hePn_16 : |tailEndpoint rPn 16 - ((cenPn 16 : ℚ) : ℝ)| ≤ ((radPn 16 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 16 (by decide)
    (A := -147115078762761346786687) (Z := 1000000000) (E := 8192000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPn, kPn, exponentQ]) (by norm_num [radPn, kPn, exponentQ])
theorem hePn_17 : |tailEndpoint rPn 17 - ((cenPn 17 : ℚ) : ℝ)| ≤ ((radPn 17 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 17 (by decide)
    (A := 160768614488468621880872) (Z := 738631771) (E := 321537228982988115246160)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPn, kPn, exponentQ]) (by norm_num [radPn, kPn, exponentQ])
theorem hePn_18 : |tailEndpoint rPn 18 - ((cenPn 18 : ℚ) : ℝ)| ≤ ((radPn 18 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 18 (by decide)
    (A := 147086930925782126106158) (Z := 1000000000) (E := 8193000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPn, kPn, exponentQ]) (by norm_num [radPn, kPn, exponentQ])
theorem hePn_19 : |tailEndpoint rPn 19 - ((cenPn 19 : ℚ) : ℝ)| ≤ ((radPn 19 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 19 (by decide)
    (A := -160737856168869596950923) (Z := 738631771) (E := 321475712343790804018035)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPn, kPn, exponentQ]) (by norm_num [radPn, kPn, exponentQ])
theorem hePn_20 : |tailEndpoint rPn 20 - ((cenPn 20 : ℚ) : ℝ)| ≤ ((radPn 20 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 20 (by decide)
    (A := -147058791908788040277550) (Z := 1000000000) (E := 8194000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPn, kPn, exponentQ]) (by norm_num [radPn, kPn, exponentQ])
theorem hePn_21 : |tailEndpoint rPn 21 - ((cenPn 21 : ℚ) : ℝ)| ≤ ((radPn 21 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 21 (by decide)
    (A := 160707107486649435657516) (Z := 738631771) (E := 321414214979351220062994)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPn, kPn, exponentQ]) (by norm_num [radPn, kPn, exponentQ])
theorem hePn_22 : |tailEndpoint rPn 22 - ((cenPn 22 : ℚ) : ℝ)| ≤ ((radPn 22 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 22 (by decide)
    (A := 147030661707939500997990) (Z := 1000000000) (E := 8195000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPn, kPn, exponentQ]) (by norm_num [radPn, kPn, exponentQ])
theorem hePn_23 : |tailEndpoint rPn 23 - ((cenPn 23 : ℚ) : ℝ)| ≤ ((radPn 23 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 23 (by decide)
    (A := -160676368437612971102565) (Z := 738631771) (E := 321352736881279029584865)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPn, kPn, exponentQ]) (by norm_num [radPn, kPn, exponentQ])
theorem hePn_24 : |tailEndpoint rPn 24 - ((cenPn 24 : ℚ) : ℝ)| ≤ ((radPn 24 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 24 (by decide)
    (A := -147002540319399059696540) (Z := 1000000000) (E := 8196000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPn, kPn, exponentQ]) (by norm_num [radPn, kPn, exponentQ])
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
theorem errPn : tailError rPn ((49157 : ℚ) : ℝ) ≤
    ((tailErrorUpperQ kqPn 49157 cenPn radPn : ℚ) : ℝ) :=
  tailError_le_Q rPn kqPn 49157 cenPn radPn
    (fun i => by fin_cases i <;> norm_num [rPn, kPn, kqPn])
    (by decide +kernel) (by decide +kernel) hePn
theorem leadValPn : tailLeadingUpperQ cenPn radPn = (515384284636105109396047409236460206162294940711577579353829876445842494565689104706656525064525487171592303295551235026687 / 8521703954887500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by decide +kernel
theorem errValPn : tailErrorUpperQ kqPn 49157 cenPn radPn = (380836436840811093965224730997327437381977838257999485209303083715182470735159185510066396987843679875313916703130418858354752210758411571140166293154724250896457 / 7521523528312364599285141403114007830282968078253528250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by decide +kernel
end KsIndex.NegSignProd
