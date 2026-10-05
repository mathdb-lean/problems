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

import MathdbUtil

/-!
Converted from another corpus. `source` names it, `source_version`
pins the revision, and `source_locator` points at the one
declaration this came from. Every `source_` field describes that
declaration as it stands there, not as it stands here.

Read `track` for whether the problem is solved, which is a fact
about mathematics. `source_has_lean_proof` is a different claim --
whether that corpus holds a machine-checked proof -- and is false
for almost every problem, because it is a statement repository.

- problem_id: NSixStandardDeviations_six_standard_deviations
- collection: wikipedia
- question_id: wikipedia:SixStandardDeviations
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/SixStandardDeviations.lean#six_standard_deviations
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Six standard deviations suffice** (Spencer, 1985) For every $n$ and every family of $n$ subsets $S_1, \dots, S_n$ of $\{1, \dots, n\}$, there is a colouring $\chi : \{1, \dots, n\} \to \{-1, +1\}$ such that $\left|\sum_{j \in S_i} \chi(j)\right| \le 6\sqrt{n}$ for every $i$.
- notes: Wikipedia: SixStandardDeviations -- https://en.wikipedia.org/wiki/Discrepancy_of_hypergraphs#General_hypergraphs
- track: solved
- answer_shape: proof
- source_stem: SixStandardDeviations
- source_namespace: SixStandardDeviations
- source_theorem: six_standard_deviations
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: six_standard_deviations.variants.zero_sets
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/--
Sanity check: with no points and no sets ($n = 0$), the empty colouring works and
the bound $6\sqrt{0} = 0$ holds vacuously.
-/
@[category test, AMS 5]
theorem six_standard_deviations.variants.zero_sets (S : Fin 0 → Finset (Fin 0)) :
    ∃ χ : Fin 0 → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 6 * Real.sqrt 0 :=
  ⟨Fin.elim0, fun j => j.elim0, fun i => i.elim0⟩

abbrev Target : Prop :=
    ∀ (n : ℕ) (S : Fin n → Finset (Fin n)),
      ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
        ∀ i, |∑ j ∈ S i, χ j| ≤ 6 * Real.sqrt n

end Problem
