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

- problem_id: E780
- collection: erdos
- question_id: erdos:780
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/780.lean#erdos_780
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Suppose $n\geq kr+(t-1)(k-1)$ and the edges of the complete $r$-uniform hypergraph on $n$ vertices are $t$-coloured. Prove that some colour class must contain $k$ pairwise disjoint edges. In other words, this problem asks to determine the chromatic number of the Kneser hypergraph. When $k=2$ this was conjectured by Kneser and proved by Lovász [Lo78]. The general case was proved by Alon, Frankl, and Lovász [AFL86].
- notes: Erdos Problem 780 -- https://www.erdosproblems.com/780
- track: solved
- answer_shape: proof
- source_stem: 780
- mathdb_ref: erdos:780
- source_namespace: Erdos780
- source_theorem: erdos_780
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

abbrev Target : Prop :=
    ∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t)
        (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t),
      ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
        (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

end Problem
