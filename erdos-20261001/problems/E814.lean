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

- problem_id: E814
- collection: erdos
- question_id: erdos:814
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/814.lean#erdos_814
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $k\geq 2$ and $G$ be a graph with $n\geq k-1$ vertices and $$(k-1)(n-k+2)+\binom{k-2}{2}+1$$ edges. Does there exist some $c_k>0$ such that $G$ must contain an induced subgraph on at most $(1-c_k)n$ vertices with minimum degree at least $k$? The case $k=3$ was a problem of Erdős and Hajnal [Er91]. The question for general $k$ was a conjecture of Erdős, Faudree, Rousseau, and Schelp [EFRS90], who proved that such a subgraph exists with at most $n-c_k\sqrt{n}$ vertices. Mousset, Noever, and Skorić [MNS17] improved this to $n-c_k\frac{n}{\log n}$. The full conjecture was proved by Sauermann [Sa19], who proved this with $c_k \gg 1/k^3$.
- notes: Erdos Problem 814 -- https://www.erdosproblems.com/814
- track: solved
- answer_shape: decide
- source_stem: 814
- mathdb_ref: erdos:814
- source_namespace: Erdos814
- source_theorem: erdos_814
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Real SimpleGraph

namespace Problem

open scoped Classical in
abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ k ≥ 2, ∃ c > 0, ∀ n ≥ k - 1, ∀ G : SimpleGraph (Fin n),
          G.edgeFinset.card = (k - 1) * (n + 2 - k) + (k - 2).choose 2 + 1 →
            ∃ S : Finset (Fin n), S.Nonempty ∧ (S.card : ℝ) ≤ (1 - c) * n ∧
              k ≤ (G.induce (S : Set (Fin n))).minDegree

end Problem
