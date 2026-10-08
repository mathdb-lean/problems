# Manually selected Millennium candidates

These are unreviewed conversion candidates, not solved problems or published
MathDB formalizations. They retain the source snapshot pinned at
`e04cc601840dd7a37f89b821a67f3a9e3c38d9c3`.

The automatic adapter selected no target because these files contain several
research declarations. This package selects declarations explicitly and uses
the existing module generator; it does not change automatic conversion rules.

| Problem | Obligations | Scope |
| --- | ---: | --- |
| Riemann hypothesis | 1 | Mathlib's `RiemannHypothesis`, excluding GRH |
| P vs NP | 2 | Separate equality and inequality targets using the source's concrete complexity classes |
| Birch–Swinnerton-Dyer | 1 | Weak rank statement over ℚ; finite generation and meromorphic continuation are hypotheses |
| Navier–Stokes | 4 | Separate unforced existence and forced breakdown cases, on ℝ³ and periodic space |

BSD does not assert existence of continuation or the leading-coefficient
formula. Navier–Stokes source `solved` annotations are upstream metadata,
not a MathDB endorsement or a claim that a Clay prize has been resolved.
Each of its four cases needs a mathematical fidelity review separately.

P vs NP's derived branch locators are distinct; `original_source_locator`
retains the common source declaration. The equality branch is deliberately
derived from the source inequality, not presented as an original declaration.

These files are deliberately outside `problems/` and `benchmark.json` until
validation and human review are complete. The existing published benchmark is
unchanged. `source.jsonl` carries the targets and their conversion provenance.

After building the pinned project, compile each candidate independently:

```sh
lake exe cache get
lake build
for file in candidates/millennium/*.lean; do lake env lean "$file" || exit 1; done
```

Compilation and dependency checks establish well-formedness, not mathematical
equivalence to the informal Millennium problems. Human conversion-fidelity
review is required before publication, linking, or bounty eligibility.
