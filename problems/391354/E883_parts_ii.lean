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

- problem_id: E883_parts_ii
- collection: erdos
- question_id: erdos:883
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/883.lean#erdos_883.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that, for every $\ell\geq 1$, if $n$ is sufficiently large and $$|A| > \lfloor n/2\rfloor + \lfloor n/3\rfloor - \lfloor n/6\rfloor$$ then $G(A)$ must contain a complete $(1,\ell,\ell)$ tripartite graph on $2\ell+1$ vertices? The second question was solved by Sárközy [Sa99], who proved this with $\ell \gg \log n/\log\log n$.
- notes: Erdos Problem 883 -- https://www.erdosproblems.com/883
- track: solved
- answer_shape: decide
- source_stem: 883
- mathdb_ref: erdos:883
- source_namespace: Erdos883
- source_theorem: erdos_883.parts.ii
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter

namespace Problem

/--
The coprime graph on $\mathbb{N}$: two integers are joined by an edge if they are coprime.
-/
def coprimeGraph : SimpleGraph ℕ :=
  SimpleGraph.fromRel Nat.Coprime

open scoped Classical in
abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ l : ℕ, 1 ≤ l → ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℕ,
          A ⊆ Finset.Icc 1 n →
          n / 2 + n / 3 - n / 6 < A.card →
          (SimpleGraph.completeMultipartiteGraph (fun i : Fin 3 ↦ Fin (![1, l, l] i))).IsContained
            (coprimeGraph.induce (A : Set ℕ))

end Problem
