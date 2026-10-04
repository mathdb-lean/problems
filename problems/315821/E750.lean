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

- problem_id: E750
- collection: erdos
- question_id: erdos:750
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/750.lean#erdos_750
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f(m)$ be some function such that $f(m)\to \infty$ as $m\to \infty$. Does there exist a graph $G$ of infinite chromatic number such that every subgraph on $m$ vertices contains an independent set of size at least $\frac{m}{2}-f(m)$? Note that in [Er94b] the function $f$ generalises a (proven) result for $f(m) = \epsilon m$, where $\epsilon > 0$. Hence we should assume it is non-negative valued. The existence of such a graph was proved [UlamErdos750] by GPT 5.5 Pro (prompted by Chojecki). Indeed, this constructs a graph with infinite chromatic number such that every subgraph on $m$ vertices can be made bipartite after deleting at most $f(m)$ many vertices.
- notes: Erdos Problem 750 -- https://www.erdosproblems.com/750
- track: solved
- answer_shape: decide
- source_stem: 750
- mathdb_ref: erdos:750
- source_namespace: Erdos750
- source_theorem: erdos_750
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: genMyc_apex_adj_top genMyc_adj_level_zero
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Finset NNReal SimpleGraph

universe u

namespace Problem

/--
Vertices of the generalised Mycielskian $M_s(G)$: $s$ copies of the vertices of $G$, one per
level, and a single apex.
-/
abbrev MycVerts (s : ℕ) (V : Type u) : Type u := (Fin s × V) ⊕ Unit

/--
Adjacency of the generalised Mycielskian, before `SimpleGraph.fromRel` packages it as a graph.

Two level-`0` vertices are adjacent when the underlying vertices are; a level-`i` vertex and a
level-`i + 1` vertex are adjacent when the underlying vertices are; and the apex is adjacent to
every vertex on the top level. The relation is already symmetric and irreflexive, so `fromRel`
changes nothing about it.
-/
def MycAdj (s : ℕ) {V : Type u} (G : SimpleGraph V) : MycVerts s V → MycVerts s V → Prop
  | Sum.inl (i, u), Sum.inl (j, v) =>
      (i.val = 0 ∧ j.val = 0 ∧ G.Adj u v) ∨ (j.val = i.val + 1 ∧ G.Adj u v) ∨
        (i.val = j.val + 1 ∧ G.Adj u v)
  | Sum.inl (i, _), Sum.inr () => i.val + 1 = s
  | Sum.inr (), Sum.inl (i, _) => i.val + 1 = s
  | Sum.inr (), Sum.inr () => False

/--
The **generalised Mycielskian** $M_s(G)$. $M_2(G)$ is the classical Mycielskian, and $M_1(G)$
adds a vertex joined to everything.
-/
def genMyc (s : ℕ) {V : Type u} (G : SimpleGraph V) : SimpleGraph (MycVerts s V) :=
  .fromRel (MycAdj s G)

/--
`G` belongs to the class $M_r$, meaning it is built from $K_2$ by $r - 2$ generalised
Mycielskians. Stiebitz's theorem is about this class and not about arbitrary graphs: it is false
that $\chi(M_s(H)) = \chi(H) + 1$ for every $H$ and every $s$.
-/
def IsRecursivelyBuiltMr : ∀ (_r : ℕ) {_V : Type u} (_G : SimpleGraph _V), Prop
  | 0, _, _ => False
  | 1, _, _ => False
  | 2, _, G => Nonempty (G ≃g completeGraph (Fin 2))
  | r + 3, _, G => ∃ (W : Type u) (H : SimpleGraph W) (s : ℕ),
      1 ≤ s ∧ IsRecursivelyBuiltMr (r + 2) H ∧ Nonempty (G ≃g genMyc s H)

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- The apex of $M_s(G)$ is adjacent to every vertex on the top level. -/
@[category test, AMS 5]
theorem genMyc_apex_adj_top {V : Type u} (G : SimpleGraph V) (s : ℕ) (hs : 0 < s) (v : V) :
    (genMyc s G).Adj (Sum.inr ()) (Sum.inl (⟨s - 1, by omega⟩, v)) := by
  refine ⟨by simp, Or.inl ?_⟩
  show s - 1 + 1 = s
  omega

/-- Two level-`0` vertices of $M_s(G)$ are adjacent exactly when the underlying vertices are. -/
@[category test, AMS 5]
theorem genMyc_adj_level_zero {V : Type u} (G : SimpleGraph V) {s : ℕ} (hs : 0 < s) {u v : V}
    (huv : G.Adj u v) :
    (genMyc s G).Adj (Sum.inl (⟨0, hs⟩, u)) (Sum.inl (⟨0, hs⟩, v)) := by
  refine ⟨by simpa using huv.ne, Or.inl ?_⟩
  exact Or.inl ⟨rfl, rfl, huv⟩

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ (f : ℕ → ℝ≥0) (hf : atTop.Tendsto f atTop),
      ∃ (V : Type*) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
        ∀ (m : ℕ) (S : Set V), 0 < m → S.ncard = m →
          ∃ I ⊆ S, G.IsIndepSet I ∧ m / 2 - f m ≤ I.ncard

end Problem
