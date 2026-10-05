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

- problem_id: E447_parts_ii
- collection: erdos
- question_id: erdos:447
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/447.lean#erdos_447.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: How large can a union-free collection $\mathcal{F}$ of subsets of $[n]$ be? By union-free we mean there are no solutions to $A\cup B=C$ with distinct $A,B,C\in \mathcal{F}$. Perhaps even $$\lvert \mathcal{F}\rvert <(1+o(1))\binom{n}{\lfloor n/2\rfloor}?$$ Solved by Kleitman [Kl71], who proved $$\lvert \mathcal{F}\rvert <(1+o(1))\binom{n}{\lfloor n/2\rfloor}.$$
- notes: Erdos Problem 447 -- https://www.erdosproblems.com/447
- track: solved
- answer_shape: decide
- source_stem: 447
- mathdb_ref: erdos:447
- source_namespace: Erdos447
- source_theorem: erdos_447.parts.ii
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter

namespace Problem

/-- The largest size of a union-free collection $\mathcal{F}$ of subsets of $[n]$. -/
noncomputable def maxUnionFree (n : ℕ) : ℕ :=
  sSup { k | ∃ F : Finset (Finset (Fin n)), F.UnionFree ∧ F.card = k }

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ c : ℕ → ℝ, (c =o[atTop] (1 : ℕ → ℝ)) ∧ ∀ᶠ n : ℕ in atTop,
          (maxUnionFree n : ℝ) < (1 + c n) * (n.choose (n / 2) : ℝ)

end Problem
