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

- problem_id: E221
- collection: erdos
- question_id: erdos:221
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/221.lean#erdos_221
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is there a set $A\subset\mathbb{N}$ such that, for all large $N$, $$\lvert A\cap\{1,\ldots,N\}\rvert \ll N/\log N$$ and such that every large integer can be written as $2^k+a$ for some $k\geq 0$ and $a\in A$? Lorentz [Lo54] proved there is such a set with, for all large $N$, $$\lvert A\cap\{1,\ldots,N\}\rvert \ll \frac{\log\log N}{\log N}N$$ The answer is yes, proved by Ruzsa [Ru72].
- notes: Erdos Problem 221 -- https://www.erdosproblems.com/221
- track: solved
- answer_shape: decide
- source_stem: 221
- mathdb_ref: erdos:221
- source_namespace: Erdos221
- source_theorem: erdos_221
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Asymptotics

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ A : Set ℕ,
      ((fun N => ({a ∈ A | a ≤ N}.ncard : ℝ)) ≪ (fun N => (N : ℝ) / Real.log N)) ∧
      ∀ᶠ N in atTop, ∃ k a, 0 ≤ k ∧ a ∈ A ∧ N = 2 ^ k + a

end Problem
