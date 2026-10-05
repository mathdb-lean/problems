/-
Copyright 2025 The Formal Conjectures Authors.
Copyright 2026 The mathdb-lean Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import MathDBUtil

/-!
Converted from another corpus. `source` names it, `source_version`
pins the revision, and `source_locator` points at the one
declaration this came from. Every `source_` field describes that
declaration as it stands there, not as it stands here.

Read `track` for whether the problem is solved, which is a fact
about mathematics. `source_has_lean_proof` is a different claim --
whether that corpus holds a machine-checked proof -- and is false
for almost every problem, because it is a statement repository.

- problem_id: O105751_conjecture
- collection: oeis
- question_id: oeis:105751
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/105751.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Moll's conjecture 5.5 extends to this sequence and takes the form: (i) the $2$-adic valuation $\nu_2(a(n)) \sim n/4$ as n -> oo.
- notes: OEIS A105751 -- https://oeis.org/A105751
- track: solved
- answer_shape: proof
- source_stem: 105751
- source_namespace: OeisA105751
- source_theorem: conjecture
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4
- generator: adapters/formal_conjectures/adapter.py
-/

open Complex Filter Topology Nat

namespace Problem

/--
The primary defining sequence `a`.
a n is the imaginary part of $\prod_{k=0}^n (1 + k \cdot i)$, where $i = \sqrt{-1}$.
-/
noncomputable def a (n : ℕ) : ℤ :=
  let productTerm (k : ℕ) : ℂ := 1 + (k : ℂ) * I
  Int.floor (((Finset.range (n + 1)).prod productTerm).im)

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  delta a; norm_num [Finset.prod]

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  delta a; norm_num [Finset.prod]

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by
  delta a; norm_num [Finset.prod]

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by
  delta a; norm_num [Finset.prod]

@[category test, AMS 11]
theorem a_4 : a 4 = -40 := by
  delta a; norm_num [Finset.prod]

abbrev Target : Prop :=
    Tendsto (fun n ↦ (4 : ℚ) * (padicValInt 2 (a n) : ℚ) / (n : ℚ)) atTop (nhds 1)

end Problem
