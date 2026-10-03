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

- problem_id: E133
- collection: erdos
- question_id: erdos:133
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/133.lean#erdos_133
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f(n)$ be minimal such that every triangle-free graph $G$ with $n$ vertices and diameter $2$ contains a vertex with degree $\geq f(n)$. What is the order of growth of $f(n)$? Does $f(n)/\sqrt{n}\to \infty$? Asked by Erdős and Pach. The lower bound $f(n)\geq (1-o(1))\sqrt{n}$ follows from the fact that a graph with maximum degree $d$ and diameter $2$ has at most $1+d+d(d-1)=d^2+1$ many vertices. Hanson and Seyffarth [HaSe84] proved that $f(n)\leq (\sqrt{2}+o(1))\sqrt{n}$ using a Cayley graph on $\mathbb{Z}/n\mathbb{Z}$, with the generating set given by some symmetric complete sum-free set of size $\sim \sqrt{n}$. An alternative construction of such a complete sum-free set was given by Haviv and Levy [HaLe18]. Füredi and Seress [FuSe94] proved that $f(n)\leq (\frac{2}{\sqrt{3}}+o(1))\sqrt{n}$. In particular $f(n)/\sqrt{n}\not\to\infty$. The precise asymptotics of $f(n)$ are unknown; Alon believes that the truth is $f(n)\sim \sqrt{n}$.
- notes: Erdos Problem 133 -- https://www.erdosproblems.com/133
- track: solved
- answer_shape: decide
- source_stem: 133
- mathdb_ref: erdos:133
- source_namespace: Erdos133
- source_theorem: erdos_133
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter Asymptotics SimpleGraph

namespace Problem

open scoped Classical in
/--
`f n` is the least possible maximum degree of a triangle-free graph on `n` vertices with
diameter `2`, i.e. the largest `f` such that every such graph has a vertex of degree `≥ f`.
-/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {d | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.diam = 2 ∧ ∀ v, G.degree v ≤ d}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ Tendsto (fun n : ℕ ↦ (f n : ℝ) / √n) atTop atTop

end Problem
