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

- problem_id: E804_parts_i
- collection: erdos
- question_id: erdos:804
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/804.lean#erdos_804.parts.i
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f(m,n)$ be maximal such that any graph on $n$ vertices in which every induced subgraph on $m$ vertices has an independent set of size at least $\log n$ must contain an independent set of size at least $f(n)$. Estimate $f(n)$. In particular, is it true that $f((\log n)^2,n) \geq n^{1/2-o(1)}$? The answer is no: Alon and Sudakov [AlSu07] proved that in fact $$\frac{(\log n)^2}{\log\log n}\ll f((\log n)^2,n) \ll (\log n)^2.$$
- notes: Erdos Problem 804 -- https://www.erdosproblems.com/804
- track: solved
- answer_shape: decide
- source_stem: 804
- mathdb_ref: erdos:804
- source_namespace: Erdos804
- source_theorem: erdos_804.parts.i
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter Real

namespace Problem

/-- A graph `G` on `n` vertices in which every induced subgraph on `m` vertices has an
independent set of size at least `t`. -/
def HasLocalIndependence {n : ℕ} (G : SimpleGraph (Fin n)) (m t : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.card = m → ∃ I ⊆ S, t ≤ I.card ∧ G.IsIndepSet I

/-- `f m n` is maximal such that any graph on `n` vertices in which every induced subgraph on `m`
vertices has an independent set of size at least $\log n$ must contain an independent set of size
at least `f m n`. -/
noncomputable def f (m n : ℕ) : ℕ :=
  sInf {k | ∃ G : SimpleGraph (Fin n), HasLocalIndependence G m ⌈log n⌉₊ ∧ G.indepNum = k}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
          (n : ℝ) ^ (1 / 2 - ε : ℝ) ≤ f ⌊(log n) ^ 2⌋₊ n

end Problem
