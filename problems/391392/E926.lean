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

- problem_id: E926
- collection: erdos
- question_id: erdos:926
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/926.lean#erdos_926
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $k\geq 4$. Is it true that $$\mathrm{ex}(n;H_k) \ll_k n^{3/2},$$ where $H_k$ is the graph on vertices $x,y_1,\ldots,y_k,z_1,\ldots,z_{\binom{k}{2}}$, where $x$ is adjacent to all $y_i$ and each pair of $y_i,y_j$ is adjacent to a unique $z_i$. It is trivial that $\mathrm{ex}(n;H_k)\gg n^{3/2}$ since $H_k$ contians a $C_4$ for $k\geq 3$. Erdős [Er71] claimed a proof for $k=3$. The answer is yes, proved by Füredi [Fu91], who proved that $\mathrm{ex}(n;H_k) \ll (kn)^{3/2}$. This was improved to $\mathrm{ex}(n;H_k) \ll kn^{3/2}$ by Alon, Krivelevich, and Sudakov [AKS03]. Since each $H_k$ is 2-degenerate this is a special case of [146](https://www.erdosproblems.com/146). The extremal number of the graph $H_k$ with the vertex $x$ omitted is the subject of [1021](https://www.erdosproblems.com/1021).
- notes: Erdos Problem 926 -- https://www.erdosproblems.com/926
- track: solved
- answer_shape: decide
- source_stem: 926
- mathdb_ref: erdos:926
- source_namespace: Erdos926
- source_theorem: erdos_926
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Asymptotics SimpleGraph

namespace Problem

/-- The graph $H_k$ on the vertices $x, y_1, \ldots, y_k, z_{ij}$ ($i < j$): $x$ is adjacent to
every $y_i$, and each pair $y_i, y_j$ is adjacent to the vertex $z_{ij}$. -/
def H (k : ℕ) : SimpleGraph (Unit ⊕ (Fin k ⊕ {p : Fin k × Fin k // p.1 < p.2})) where
  Adj x y :=
    match x, y with
    | Sum.inl _, Sum.inr (Sum.inl _) => True
    | Sum.inr (Sum.inl _), Sum.inl _ => True
    | Sum.inr (Sum.inl i), Sum.inr (Sum.inr p) => i = p.1.1 ∨ i = p.1.2
    | Sum.inr (Sum.inr p), Sum.inr (Sum.inl i) => i = p.1.1 ∨ i = p.1.2
    | _, _ => False
  symm := by
    constructor
    intro x y h
    rcases x with _ | _ | _ <;> rcases y with _ | _ | _ <;> simp_all
  loopless := by
    constructor
    intro x
    rcases x with _ | _ | _ <;> simp

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ k : ℕ, 4 ≤ k →
        (fun n : ℕ => (extremalNumber n (H k) : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ)

end Problem
