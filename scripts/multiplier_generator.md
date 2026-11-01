# Multiplier certificate generator

`multiplier_generator.py` reproduces `KsIndexLean/AlphaGroupMultiplierCert.lean`
using Python 3 and its standard library. It is an optional reproduction tool;
the default Lean build does not execute it.

From the repository root, generate into a temporary file and compare:

```sh
python3 scripts/multiplier_generator.py --output /tmp/AlphaGroupMultiplierCert.lean
cmp /tmp/AlphaGroupMultiplierCert.lean KsIndexLean/AlphaGroupMultiplierCert.lean
```

The output path is required and is overwritten if it exists. Its parent directory
must already exist. Diagnostic tables are printed to standard output. Run without
Python's `-O` option to retain the script's diagnostic assertions.

## Inputs and construction

The script embeds the 25 shifts and two exponents from `AlphaRemarkTrial.lean`
and the coefficient numerators from `AlphaTrialIntegerData.lean`, with coefficient
scale `10^12`. Changes to those trial data require updating the embedded inputs.
It combines each exponent/parity group into one rational function before taking
bounds, retaining cancellation between its terms.

At cutoff 1024 it translates the variable to `y = x - 2051`, clears a common
positive denominator from numerator and denominator coefficients, and emits four
integer coefficient certificates. Exact arithmetic uses `fractions.Fraction`;
floating-point values appear only in the printed diagnostic summaries.

## Verification boundary

Positive denominator coefficients and coefficientwise lower/upper inequalities
imply the rational-function bounds for every `y >= 0`.
The generated Lean theorems prove these finite inequalities and apply
`rational_integer_coefficients_bound`. Separate Lean identity theorems identify
the rational functions with the trial multipliers. The Python sample checks are
diagnostics, not a proof of those identities or an additional trusted assumption.

This generator does not rebuild the large numerical certificate blocks or rerun
the final alpha-star proof. Byte equality checks reproduction of the committed
source; it does not substitute for compiling that source in Lean.
