module

public import KsIndexLean.ProdValid
public import KsIndexLean.NegSignEndpointBridge

@[expose] public section

/-! Tail Pp: K = 16386, c = 49159, sign +1. -/
set_option maxHeartbeats 2000000
set_option linter.style.longLine false
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial PowerArc
def kPp : Fin 25 → ℤ := ![16392,16391,16390,16389,16388,16387,16385,16384,16383,16382,16381,16380,16392,16391,16390,16389,16388,16387,16386,16385,16384,16383,16382,16381,16380]
def kqPp : Fin 25 → ℚ := ![16392,16391,16390,16389,16388,16387,16385,16384,16383,16382,16381,16380,16392,16391,16390,16389,16388,16387,16386,16385,16384,16383,16382,16381,16380]
noncomputable def rPp : Fin 25 → ℝ := fun i => ((kPp i : ℤ) : ℝ)
def cenPp : Fin 25 → ℚ := ![(-16971396168607032292431095083769589 / 2500000000000000000000000000000000000 : ℚ),(-42048006033046959320069975101676964304112417 / 5000000000000000000000000000000000000000000000 : ℚ),(8486145794917850443510061380165651 / 1250000000000000000000000000000000000 : ℚ),(4205022464689732212032762721894842161640613 / 500000000000000000000000000000000000000000000 : ℚ),(-33946374335187318776918170188366657 / 5000000000000000000000000000000000000 : ℚ),(-10513110912152246683734327217674291523496223 / 1250000000000000000000000000000000000000000000 : ℚ),(21027331519148556313991420253931099021519477 / 2500000000000000000000000000000000000000000000 : ℚ),(-33949957585766707963957526502788997 / 5000000000000000000000000000000000000 : ℚ),(-42056882816076907518370710855224822161165293 / 5000000000000000000000000000000000000000000000 : ℚ),(339517496810161853984577827422351 / 50000000000000000000000000000000000 : ℚ),(2102955149103181370297182679185168419724733 / 250000000000000000000000000000000000000000000 : ℚ),(-33953542089696253189497491049826143 / 5000000000000000000000000000000000000 : ℚ),(-602437271293242929413252879127957 / 250000000000000000000000000000000000 : ℚ),(-1945362239108558952615680645739739041511893 / 1000000000000000000000000000000000000000000000 : ℚ),(1204958002806642562530555748623609 / 500000000000000000000000000000000000 : ℚ),(2431871250311585142514051358872000271966919 / 1250000000000000000000000000000000000000000000 : ℚ),(-241008295798915168307585407598241 / 100000000000000000000000000000000000 : ℚ),(-9728158935871611000715747646016518678208903 / 5000000000000000000000000000000000000000000000 : ℚ),(6025624855776450384187900151340089 / 2500000000000000000000000000000000000 : ℚ),(1216104124932376654246811036535475753357449 / 625000000000000000000000000000000000000000000 : ℚ),(-12052084792937918289154996893963217 / 5000000000000000000000000000000000000 : ℚ),(-2432376798012243011967515237165552669884473 / 1250000000000000000000000000000000000000000000 : ℚ),(6026460017075449194850348898522301 / 2500000000000000000000000000000000000 : ℚ),(1946036302736385965874917615540235265191781 / 1000000000000000000000000000000000000000000000 : ℚ),(-12053755435241950301283356374635801 / 5000000000000000000000000000000000000 : ℚ)]
def radPp : Fin 25 → ℚ := ![(167940469546641 / 1250000000000000000000000000000000000 : ℚ),(175275574509873434935324499015359343 / 5000000000000000000000000000000000000000000000 : ℚ),(134319593204951 / 1000000000000000000000000000000000000 : ℚ),(17528482272052404806441213911706163 / 500000000000000000000000000000000000000000000 : ℚ),(335717036931473 / 2500000000000000000000000000000000000 : ℚ),(10955879534247519064218695190133593 / 312500000000000000000000000000000000000000000 : ℚ),(87651661996331121918326225577176023 / 2500000000000000000000000000000000000000000000 : ℚ),(81922161809 / 610351562500000000000000000000000 : ℚ),(175312577055110103652401654551779587 / 5000000000000000000000000000000000000000000000 : ℚ),(670942517377519 / 5000000000000000000000000000000000000 : ℚ),(8766091586789216244629614193281737 / 250000000000000000000000000000000000000000000 : ℚ),(67077870521571 / 500000000000000000000000000000000000 : ℚ),(167941855453359 / 1250000000000000000000000000000000000 : ℚ),(5267475122310172936767573514515843 / 1000000000000000000000000000000000000000000000 : ℚ),(134320701795049 / 1000000000000000000000000000000000000 : ℚ),(13169600040707581093940332569501927 / 2500000000000000000000000000000000000000000000 : ℚ),(335719808068527 / 2500000000000000000000000000000000000 : ℚ),(5268204980072398452636708895154937 / 1000000000000000000000000000000000000000000000 : ℚ),(671275743298863 / 5000000000000000000000000000000000000 : ℚ),(329285625856259572469543207676207 / 62500000000000000000000000000000000000000000 : ℚ),(81922838191 / 610351562500000000000000000000000 : ℚ),(26344675585940941332135967985168517 / 5000000000000000000000000000000000000000000000 : ℚ),(670948057622481 / 5000000000000000000000000000000000000 : ℚ),(329331268159900313598619593583241 / 62500000000000000000000000000000000000000000 : ℚ),(67078424478429 / 500000000000000000000000000000000000 : ℚ)]
theorem hePp_0 : |tailEndpoint rPp 0 - ((cenPp 0 : ℚ) : ℝ)| ≤ ((radPp 0 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 0 (by decide)
    (A := -414127587511813485344842) (Z := 1000000000) (E := 8196000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPp, kPp, exponentQ]) (by norm_num [radPp, kPp, exponentQ])
theorem hePp_1 : |tailEndpoint rPp 1 - ((cenPp 1 : ℚ) : ℝ)| ≤ ((radPp 1 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 1 (by decide)
    (A := -712874753267921831963609) (Z := 719689657) (E := 2138624259809663352654527)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPp, kPp, exponentQ]) (by norm_num [radPp, kPp, exponentQ])
theorem hePp_2 : |tailEndpoint rPp 2 - ((cenPp 2 : ℚ) : ℝ)| ≤ ((radPp 2 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 2 (by decide)
    (A := 414199972647257268815756) (Z := 1000000000) (E := 8195000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPp, kPp, exponentQ]) (by norm_num [radPp, kPp, exponentQ])
theorem hePp_3 : |tailEndpoint rPp 3 - ((cenPp 3 : ℚ) : ℝ)| ≤ ((radPp 3 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 3 (by decide)
    (A := 712999363860782349447010) (Z := 719689657) (E := 2138998091588244185415070)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPp, kPp, exponentQ]) (by norm_num [radPp, kPp, exponentQ])
theorem hePp_4 : |tailEndpoint rPp 4 - ((cenPp 4 : ℚ) : ℝ)| ≤ ((radPp 4 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 4 (by decide)
    (A := -414272379270556019959473) (Z := 1000000000) (E := 8194000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPp, kPp, exponentQ]) (by norm_num [radPp, kPp, exponentQ])
theorem hePp_5 : |tailEndpoint rPp 5 - ((cenPp 5 : ℚ) : ℝ)| ≤ ((radPp 5 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 5 (by decide)
    (A := -713124011447118577206684) (Z := 719689657) (E := 2139372034347252149004432)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPp, kPp, exponentQ]) (by norm_num [radPp, kPp, exponentQ])
theorem hePp_6 : |tailEndpoint rPp 6 - ((cenPp 6 : ℚ) : ℝ)| ≤ ((radPp 6 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 6 (by decide)
    (A := 713248696042429855314458) (Z := 719689657) (E := 2139746088133185263638094)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPp, kPp, exponentQ]) (by norm_num [radPp, kPp, exponentQ])
theorem hePp_7 : |tailEndpoint rPp 7 - ((cenPp 7 : ℚ) : ℝ)| ≤ ((radPp 7 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 7 (by decide)
    (A := -414417257016732591287733) (Z := 1000000000) (E := 8192000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPp, kPp, exponentQ]) (by norm_num [radPp, kPp, exponentQ])
theorem hePp_8 : |tailEndpoint rPp 8 - ((cenPp 8 : ℚ) : ℝ)| ≤ ((radPp 8 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 8 (by decide)
    (A := -713373417662223910645061) (Z := 719689657) (E := 2140120252992566709940243)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPp, kPp, exponentQ]) (by norm_num [radPp, kPp, exponentQ])
theorem hePp_9 : |tailEndpoint rPp 9 - ((cenPp 9 : ℚ) : ℝ)| ≤ ((radPp 9 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 9 (by decide)
    (A := 414489728157629675023900) (Z := 1000000000) (E := 8191000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPp, kPp, exponentQ]) (by norm_num [radPp, kPp, exponentQ])
theorem hePp_10 : |tailEndpoint rPp 10 - ((cenPp 10 : ℚ) : ℝ)| ≤ ((radPp 10 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 10 (by decide)
    (A := 713498176322016862438820) (Z := 719689657) (E := 2140494528971944845631860)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPp, kPp, exponentQ]) (by norm_num [radPp, kPp, exponentQ])
theorem hePp_11 : |tailEndpoint rPp 11 - ((cenPp 11 : ℚ) : ℝ)| ≤ ((radPp 11 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 11 (by decide)
    (A := -414562220822420259999727) (Z := 1000000000) (E := 8190000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPp, kPp, exponentQ]) (by norm_num [radPp, kPp, exponentQ])
theorem hePp_12 : |tailEndpoint rPp 12 - ((cenPp 12 : ℚ) : ℝ)| ≤ ((radPp 12 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 12 (by decide)
    (A := -147002540319399059696540) (Z := 1000000000) (E := 8196000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPp, kPp, exponentQ]) (by norm_num [radPp, kPp, exponentQ])
theorem hePp_13 : |tailEndpoint rPp 13 - ((cenPp 13 : ℚ) : ℝ)| ≤ ((radPp 13 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 13 (by decide)
    (A := -160676368437612971102565) (Z := 738631771) (E := 321352736881279029584865)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPp, kPp, exponentQ]) (by norm_num [radPp, kPp, exponentQ])
theorem hePp_14 : |tailEndpoint rPp 14 - ((cenPp 14 : ℚ) : ℝ)| ≤ ((radPp 14 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 14 (by decide)
    (A := 147030661707939500997990) (Z := 1000000000) (E := 8195000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPp, kPp, exponentQ]) (by norm_num [radPp, kPp, exponentQ])
theorem hePp_15 : |tailEndpoint rPp 15 - ((cenPp 15 : ℚ) : ℝ)| ≤ ((radPp 15 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 15 (by decide)
    (A := 160707107486649435657516) (Z := 738631771) (E := 321414214979351220062994)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPp, kPp, exponentQ]) (by norm_num [radPp, kPp, exponentQ])
theorem hePp_16 : |tailEndpoint rPp 16 - ((cenPp 16 : ℚ) : ℝ)| ≤ ((radPp 16 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 16 (by decide)
    (A := -147058791908788040277550) (Z := 1000000000) (E := 8194000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPp, kPp, exponentQ]) (by norm_num [radPp, kPp, exponentQ])
theorem hePp_17 : |tailEndpoint rPp 17 - ((cenPp 17 : ℚ) : ℝ)| ≤ ((radPp 17 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 17 (by decide)
    (A := -160737856168869596950923) (Z := 738631771) (E := 321475712343790804018035)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPp, kPp, exponentQ]) (by norm_num [radPp, kPp, exponentQ])
theorem hePp_18 : |tailEndpoint rPp 18 - ((cenPp 18 : ℚ) : ℝ)| ≤ ((radPp 18 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 18 (by decide)
    (A := 147086930925782126106158) (Z := 1000000000) (E := 8193000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPp, kPp, exponentQ]) (by norm_num [radPp, kPp, exponentQ])
theorem hePp_19 : |tailEndpoint rPp 19 - ((cenPp 19 : ℚ) : ℝ)| ≤ ((radPp 19 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 19 (by decide)
    (A := 160768614488468621880872) (Z := 738631771) (E := 321537228982988115246160)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPp, kPp, exponentQ]) (by norm_num [radPp, kPp, exponentQ])
theorem hePp_20 : |tailEndpoint rPp 20 - ((cenPp 20 : ℚ) : ℝ)| ≤ ((radPp 20 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 20 (by decide)
    (A := -147115078762761346786687) (Z := 1000000000) (E := 8192000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPp, kPp, exponentQ]) (by norm_num [radPp, kPp, exponentQ])
theorem hePp_21 : |tailEndpoint rPp 21 - ((cenPp 21 : ℚ) : ℝ)| ≤ ((radPp 21 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 21 (by decide)
    (A := -160799382449644016681172) (Z := 738631771) (E := 321598764905338166214987)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPp, kPp, exponentQ]) (by norm_num [radPp, kPp, exponentQ])
theorem hePp_22 : |tailEndpoint rPp 22 - ((cenPp 22 : ℚ) : ℝ)| ≤ ((radPp 22 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 22 (by decide)
    (A := 147143235423567431808422) (Z := 1000000000) (E := 8191000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPp, kPp, exponentQ]) (by norm_num [radPp, kPp, exponentQ])
theorem hePp_23 : |tailEndpoint rPp 23 - ((cenPp 23 : ℚ) : ℝ)| ≤ ((radPp 23 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 23 (by decide)
    (A := 160830160056595628511605) (Z := 738631771) (E := 321660320119240651244080)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPp, kPp, exponentQ]) (by norm_num [radPp, kPp, exponentQ])
theorem hePp_24 : |tailEndpoint rPp 24 - ((cenPp 24 : ℚ) : ℝ)| ≤ ((radPp 24 : ℚ) : ℝ) :=
  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) 24 (by decide)
    (A := -147171400912044253302711) (Z := 1000000000) (E := 8190000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [cenPp, kPp, exponentQ]) (by norm_num [radPp, kPp, exponentQ])
theorem hePp : ∀ i, |tailEndpoint rPp i - ((cenPp i : ℚ) : ℝ)| ≤ ((radPp i : ℚ) : ℝ) := by
  intro i
  fin_cases i
  · exact hePp_0
  · exact hePp_1
  · exact hePp_2
  · exact hePp_3
  · exact hePp_4
  · exact hePp_5
  · exact hePp_6
  · exact hePp_7
  · exact hePp_8
  · exact hePp_9
  · exact hePp_10
  · exact hePp_11
  · exact hePp_12
  · exact hePp_13
  · exact hePp_14
  · exact hePp_15
  · exact hePp_16
  · exact hePp_17
  · exact hePp_18
  · exact hePp_19
  · exact hePp_20
  · exact hePp_21
  · exact hePp_22
  · exact hePp_23
  · exact hePp_24
theorem leadPp : tailLeading rPp ≤ ((tailLeadingUpperQ cenPp radPp : ℚ) : ℝ) :=
  tailLeading_le_Q rPp cenPp radPp (by decide +kernel) hePp
theorem errPp : tailError rPp ((49159 : ℚ) : ℝ) ≤
    ((tailErrorUpperQ kqPp 49159 cenPp radPp : ℚ) : ℝ) :=
  tailError_le_Q rPp kqPp 49159 cenPp radPp
    (fun i => by fin_cases i <;> norm_num [rPp, kPp, kqPp])
    (by decide +kernel) (by decide +kernel) hePp
theorem leadValPp : tailLeadingUpperQ cenPp radPp = (83058262331314988720082933804291791701684095284532434525356907046753601571286789376619134356684305206436004989619841414027 / 8521703954887500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by decide +kernel
theorem errValPp : tailErrorUpperQ kqPp 49159 cenPp radPp = (47604959835677399907999560812428193174605770115804346049135466025301378735388270471191857472834379089899097640845857394659230706942595276400649271207113025215061 / 940190441039045574910642675389250978785371009781691031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by decide +kernel
end KsIndex.NegSignProd
