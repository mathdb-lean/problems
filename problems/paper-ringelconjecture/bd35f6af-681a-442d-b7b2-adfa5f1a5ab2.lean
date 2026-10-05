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

- problem_id: RRingelConjecture_ringel_conjecture
- collection: paper
- question_id: paper:RingelConjecture
- source: formal-conjectures
- source_locator: FormalConjectures/Paper/RingelConjecture.lean#ringel_conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: For any tree $T$ with $n$ edges, the complete graph $K_{2n+1}$ decomposes into $2n+1$ edge-disjoint copies of $T$. A "copy" of $T$ is the image $T.\text{map}(f_i)$ of $T$ under a vertex embedding $f_i : V \hookrightarrow \text{Fin}(2n+1)$; the copies are pairwise edge-disjoint and together cover every edge of $K_{2n+1}$.
- notes: Problem from RingelConjecture
- track: open
- answer_shape: proof
- source_stem: RingelConjecture
- source_namespace: RingelConjecture
- source_theorem: ringel_conjecture
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open SimpleGraph

abbrev Target : Prop :=
    ∀ {V : Type} [Finite V]
        (T : SimpleGraph V) (hT : T.IsTree)
        (n : ℕ) (hn : T.edgeSet.ncard = n),
      ∃ f : Fin (2 * n + 1) → (V ↪ Fin (2 * n + 1)),
        Pairwise (fun i j => Disjoint (T.map (f i)).edgeSet (T.map (f j)).edgeSet) ∧
        ⨆ i, T.map (f i) = (⊤ : SimpleGraph (Fin (2 * n + 1)))

end Problem
