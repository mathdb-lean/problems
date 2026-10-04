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

- problem_id: E1020
- collection: erdos
- question_id: erdos:1020
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1020.lean#erdos_1020
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f(n;r,k)$ be the maximal number of edges in an $r$-uniform hypergraph which contains no set of $k$ many independent edges. For all $r\geq 3$, $$f(n;r,k)=\max\left(\binom{rk-1}{r}, \binom{n}{r}-\binom{n-k+1}{r}\right).$$ Note: the source states the formula with no range on `n` or `k`, but some restriction is needed: e.g. for `r = 3`, `k = 2`, `n = 4` no two disjoint triples fit in `4` vertices, so the left-hand side is `4.choose 3 = 4` while the right-hand side is `5.choose 3 = 10`. We require `k ≥ 1` and `n ≥ r*k - 1`: this is the smallest `n` accommodating the construction counted by the first term (all `r`-subsets of a fixed `(r*k - 1)`-set), and at `n = r*k - 1` the equality holds trivially, since the complete `r`-uniform hypergraph has no `k`-matching. The source's commentary likewise calls the case `n < k*r` trivial.
- notes: Erdos Problem 1020 -- https://www.erdosproblems.com/1020
- track: open
- answer_shape: proof
- source_stem: 1020
- mathdb_ref: erdos:1020
- source_namespace: Erdos1020
- source_theorem: erdos_1020
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- The maximum number of edges in an `r`-uniform hypergraph on `n` vertices containing no
matching of size `k` (i.e. no `k` pairwise vertex-disjoint edges). -/
noncomputable def f (n r k : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ H : Hypergraph (Fin n),
    H.vertexSet = Set.univ ∧
    (∀ e ∈ H.edgeSet, e.ncard = r) ∧
    (¬ ∃ M ⊆ H.edgeSet, M.ncard = k ∧ M.PairwiseDisjoint id) ∧
    H.edgeSet.ncard = m}

abbrev Target : Prop :=
    ∀ (r : ℕ) (hr : 3 ≤ r) (n k : ℕ) (hk : 0 < k)
        (hrk : r * k - 1 ≤ n),
      f n r k = max ((r * k - 1).choose r)
        (n.choose r - (n - k + 1).choose r)

end Problem
