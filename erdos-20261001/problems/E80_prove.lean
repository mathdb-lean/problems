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

- problem_id: E80_prove
- collection: erdos
- question_id: erdos:80
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/80.lean#erdos_80
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $c>0$ and let $f_c(n)$ be the maximal $m$ such that every graph $G$ with $n$ vertices and at least $cn^2$ edges, where each edge is contained in at least one triangle, must contain a book of size $m$, that is, an edge shared by at least $m$ different triangles. Estimate $f_c(n)$. In particular, is it true that $f_c(n)>n^\epsilon$ for some $\epsilon>0$? The bound $c < 1/2$ is what makes the hypothesis satisfiable: a simple graph on $n$ vertices has at most $n(n-1)/2$ edges, so no graph has $cn^2$ of them once $c \geq 1/2$.
- notes: Erdos Problem 80 -- https://www.erdosproblems.com/80
- track: open
- answer_shape: prove
- pair_id: E80
- pair_role: prove
- source_stem: 80
- mathdb_ref: erdos:80
- source_namespace: Erdos80
- source_theorem: erdos_80
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: bookNumber_eq_zero_iff bookNumber_bot everyEdgeInTriangle_bot
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Finset SimpleGraph

open scoped Topology

namespace Problem

variable {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]

/-- The size of the largest *book* in `G`: the greatest number of triangles sharing a single
edge. `Finset.sup` gives `0` on a graph with no edges, which is the right answer there. -/
noncomputable def bookNumber : ℕ :=
  G.edgeFinset.sup fun e => #(G.trianglesContaining e)

/-- Every edge of `G` lies in at least one triangle. -/
def EveryEdgeInTriangle : Prop :=
  ∀ e ∈ G.edgeFinset, (G.trianglesContaining e).Nonempty

/-- The graphs the problem quantifies over: `n` vertices, at least $cn^2$ edges, and every
edge in a triangle. -/
def Admissible (c : ℝ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  c * (n : ℝ) ^ 2 ≤ #G.edgeFinset ∧ EveryEdgeInTriangle G

open Classical in
/-- $f_c(n)$, the largest book size forced on every admissible graph, which is the least book
number among them.

`sInf` of the empty set is `0`, so `f c n = 0` when no graph on `n` vertices has $cn^2$ edges
at all. A simple graph has at most $n(n-1)/2$ edges, so that happens for every `n` once
$c \geq 1/2$. The statements below therefore restrict `c` to the feasible range; without that
they are false at, say, `c = 2` for reasons unrelated to the question. -/
noncomputable def f (c : ℝ) (n : ℕ) : ℕ :=
  sInf {m | ∃ G : SimpleGraph (Fin n), Admissible c G ∧ bookNumber G = m}

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- A book is counted by triangles, so `bookNumber` is `0` exactly when no edge lies in one. -/
@[category API, AMS 5]
theorem bookNumber_eq_zero_iff :
    bookNumber G = 0 ↔ ∀ e ∈ G.edgeFinset, G.trianglesContaining e = ∅ := by
  simp [bookNumber, Finset.card_eq_zero]

/-- On a graph with no edges there is no book. -/
@[category test, AMS 5]
theorem bookNumber_bot {n : ℕ} : bookNumber (⊥ : SimpleGraph (Fin n)) = 0 := by
  simp [bookNumber]

/-- `EveryEdgeInTriangle` holds vacuously on a graph with no edges, so the admissible set is
nonempty only through the edge count. -/
@[category API, AMS 5]
theorem everyEdgeInTriangle_bot {n : ℕ} :
    EveryEdgeInTriangle (⊥ : SimpleGraph (Fin n)) := by
  simp [EveryEdgeInTriangle]

abbrev Target : Prop :=
    ∀ c : ℝ, 0 < c → c < 1 / 2 →
      ∃ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ ε < f c n

end Problem
