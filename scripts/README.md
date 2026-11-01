# Checks and certificate generators

These optional tools supplement the build and comparator workflow in the
[repository README](../README.md#building). Run commands from the repository root.
Generating a certificate or running a Python diagnostic does not replace checking
the resulting proof in Lean.

## Lean checks

The 54 `.lean` files in this directory were exercised in the full source build.
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

For the recorded production comparison, 190 of 566 files are byte-identical;
372 energy files retain the original windows and theorem statements but use
optimized proofs, and four tail files use exact center-radius proof replacements.
This generator therefore does not reproduce all committed proof bodies byte for
byte. Those counts describe the upper-bound production generator, not the
separate multiplier generator.

[`negsign_prod_module_order.txt`](negsign_prod_module_order.txt) lists production
build targets. The optional [`negsign_gate_driver.sh`](negsign_gate_driver.sh)
builds the base targets and then invokes Lake once per listed target, writing a
log. It requires Bash, a working systemd user session, GNU `time`, `nice`, `free`,
and `awk`, in addition to the pinned Lean dependencies. Its default systemd memory
cap is 12G, configurable through `MEMCAP`, with swap disabled for each scope.
Lake may still build dependencies concurrently within a target. This specialized
driver does not run the combined comparator or establish axiom or fidelity checks;
use the root README for the primary verification workflow.

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
