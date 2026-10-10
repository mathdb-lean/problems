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

- problem_id: E914
- collection: erdos
- question_id: erdos:914
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/914.lean#erdos_914
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $r\geq 2$ and $m\geq 1$. Every graph with $rm$ vertices and minimum degree at least $m(r-1)$ contains $m$ vertex disjoint copies of $K_r$. When $r=2$ this follows from Dirac's theorem. Corrádi and Hajnal [CoHa63] proved this when $r=3$. Hajnal and Szemerédi [HaSz70] proved this for all $r\geq 4$. A shorter proof was given by Kierstead and Kostochka [KiKo08].
- notes: Erdos Problem 914 -- https://www.erdosproblems.com/914
- track: solved
- answer_shape: proof
- source_stem: 914
- mathdb_ref: erdos:914
- source_namespace: Erdos914
- source_theorem: erdos_914
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

abbrev Target : Prop :=
    ∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type*} [Fintype V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m)
        (hdeg : m * (r - 1) ≤ G.minDegree),
      ∃ K : Fin m → Finset V, (∀ i, G.IsNClique r (K i)) ∧
        Pairwise fun i j => Disjoint (K i) (K j)

end Problem
