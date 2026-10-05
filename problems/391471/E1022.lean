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

- problem_id: E1022
- collection: erdos
- question_id: erdos:1022
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1022.lean#erdos_1022
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is there a constant $c_t$, where $c_t\to \infty$ as $t\to \infty$, such that if $\mathcal{F}$ is a finite family of finite sets, all of size at least $t$, and for every set $X$ there are $<c_t\lvert X\rvert$ many $A\in \mathcal{F}$ with $A\subseteq X$, then $\mathcal{F}$ has chromatic number $2$ (in other words, has property B)? This is false, and $c_t<2$ for all $t$: a counterexample is provided by Wood [Wo13b], who constructs, for any $r\geq 2$, a triangle-free $2$-degenerate $r$-uniform hypergraph with chromatic number $3$. A similar counterexample was found independently by KoishiChan in the comments. This was formalized in Lean by Alexeev using Aristotle.
- notes: Erdos Problem 1022 -- https://www.erdosproblems.com/1022
- track: solved
- answer_shape: decide
- source_stem: 1022
- mathdb_ref: erdos:1022
- source_namespace: Erdos1022
- source_theorem: erdos_1022
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

/-- `SparseImpliesPropertyB t c` asserts that every finite family `F` of finite sets, all of
size at least `t`, such that for every nonempty finite set `X` there are `< c * |X|` many
`A ∈ F` with `A ⊆ X`, has property B. -/
def SparseImpliesPropertyB (t : ℕ) (c : ℝ) : Prop :=
  ∀ F : Finset (Finset ℕ), (∀ A ∈ F, t ≤ A.card) →
    (∀ X : Finset ℕ, X.Nonempty → ((F.filter (· ⊆ X)).card : ℝ) < c * (X.card : ℝ)) →
    F.HasPropertyB

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ c : ℕ → ℝ, Filter.Tendsto c Filter.atTop Filter.atTop ∧
          ∀ t : ℕ, SparseImpliesPropertyB t (c t)

end Problem
