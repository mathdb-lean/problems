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

- problem_id: E628
- collection: erdos
- question_id: erdos:628
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/628.lean#erdos_628
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $G$ be a graph with chromatic number $k$ containing no $K_k$. If $a,b\geq 2$ and $a+b=k+1$ then must there exist two disjoint subgraphs of $G$ with chromatic numbers $\geq a$ and $\geq b$ respectively?
- notes: Erdos Problem 628 -- https://www.erdosproblems.com/628
- track: open
- answer_shape: proof
- source_stem: 628
- mathdb_ref: erdos:628
- source_namespace: Erdos628
- source_theorem: erdos_628
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open SimpleGraph

abbrev Target : Prop :=
    ∀ (V : Type*) [Fintype V] (G : SimpleGraph V) (k : ℕ)
        (hG_chrom : G.chromaticNumber = (k : ℕ∞))
        (hG_clique : G.CliqueFree k)
        (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1),
      ∃ (s : Set V),
        (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
        (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)

end Problem
