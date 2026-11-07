# Checks and certificate generators

These optional tools supplement the build and comparator workflow in the
[repository README](../README.md#building). Run commands from the repository root.
Generating a certificate or running a Python diagnostic does not replace checking
the resulting proof in Lean.

## Lean checks

The 54 `.lean` files in this directory were exercised in the original published
snapshot's local full-source build. The later hosted cold-build diagnostic checks
the selected Solution closure; it does not rerun all these standalone scripts.
The 50 `audit_stage5*.lean` files inspect declarations and axiom dependencies in
the spectral, index, and nullity arguments. The historical `stage5` filename label
refers to this part of the development; it is not a separate build workflow.
An axiom report displays dependencies for inspection; it does not itself enforce
the comparator's permitted-axiom list.

For example, run a bracketing audit with the pinned toolchain and dependencies:

```sh
lake env lean -j 1 -M 6000 -DElab.async=false scripts/audit_stage5_bracketing.lean
```

The four remaining Lean checks concern cutoff limits
(`check_cutoff_limit.lean`), negative-form approximation
(`check_negative_approximation.lean`), negative-space density
(`check_negative_density.lean`), and the paper's arc-estimate proof route
(`check_task_b_route.lean`). The last check loads the proof bodies of the relevant
project modules explicitly, checks required intermediate dependencies, and rejects
the specified alternative proof dependencies. It stops traversal at external
library modules, which cannot depend on project declarations.

These are supplementary checks, not additional mathematical assumptions. Their
resource requirements depend on the imported modules; the command above limits
Lean to one worker and a 6,000 MB memory threshold.

## Certificate generators

### Multiplier certificates

[`multiplier_generator.py`](multiplier_generator.py) generates the source of
`KsIndexLean/AlphaGroupMultiplierCert.lean`. Its
[reproduction guide](multiplier_generator.md) describes the embedded inputs,
temporary output command, byte comparison, and verification boundary. It requires
Python 3 and its standard library. The default Lean build does not run it.

### Upper-bound certificates

[`negsign_generator.py`](negsign_generator.py) generates certificate data and
baseline proof templates for the upper bound on the critical phase.
[`negsign_generator_record.json`](negsign_generator_record.json) records input
hashes, commands using fresh output directories, and the reproduction boundaries.
Do not overwrite the committed optimized proofs with the generated templates.

In the historical production comparison recorded by that file, 190 of 566 files
were byte-identical;
372 energy files retained the original windows and theorem statements but used
optimized proofs, and four tail files used exact center-radius proof replacements.
This generator therefore does not reproduce all committed proof bodies byte for
byte. Those counts describe the historical upper-bound production comparison, not the
current optimized candidate or the separate multiplier generator. Later changes
include different proof lookup structures, a smaller certified energy window,
and private imports that constrain compilation order. The committed Lean source
is the input to verification; this generator alone does not reconstruct it.

[`negsign_prod_module_order.txt`](negsign_prod_module_order.txt) lists production
build targets. The optional [`negsign_gate_driver.sh`](negsign_gate_driver.sh)
builds the base targets and then invokes Lake once per listed target, writing a
log. It requires Bash, a working systemd user session, GNU `time`, `nice`, `free`,
and `awk`, in addition to the pinned Lean dependencies. Its default systemd memory
cap is 12G, configurable through `MEMCAP`, with swap disabled for each scope.
Lake may still build dependencies concurrently within a target. This specialized
driver does not run the combined comparator or establish axiom or fidelity checks;
use the root README for the primary verification workflow.

### Compilation ordering for energy certificates

The committed `ProdEnergyP` modules include private predecessor imports that
arrange compilation into eight independent chains. This limits concurrent
compilation within that family, not all Lake work. Ordinary builds already use
these imports; users do not need to run a preprocessing command.

[`stride_stage.py`](stride_stage.py) applies this import-only transform to an
unstaged copy of the family. See [STRIDED_STAGING.txt](STRIDED_STAGING.txt) for
the command and regeneration boundary. It edits files in place and refuses input
that already contains the expected staging imports. It does not reconstruct the
other optimized proof bodies, run Lean, or establish a verification verdict.
Use a separate working copy when regenerating baseline templates and applying it.

## Python diagnostics

Run these finite examples with ordinary Python 3, without `-O`, which disables
their assertions:

```sh
python3 scripts/check_task_b_rationals.py
python3 scripts/check_negative_approximation.py
```

`check_task_b_rationals.py` checks exact-rational identities and inequalities for
the arc estimates, parameter examples with denominators 2 through 20, and named
and near-endpoint tail enclosures. It uses the analytic integral-test bound; it
does not prove that bound, cover all real parameters, or check the period-2298
arithmetic results.

`check_negative_approximation.py` checks finite examples of stability of negative
quadratic forms in dimensions 1 through 6, together with unit-phase invariance
and the dimension-zero case. These diagnostics are examples and cross-checks,
not proofs of the general estimates or density theorems.
