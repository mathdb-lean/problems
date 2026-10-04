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

- problem_id: E78
- collection: erdos
- question_id: erdos:78
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/78.lean#erdos_78
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $R(k)$ be the Ramsey number for $K_k$. Give a constructive proof that $R(k) > C^k$ for some constant $C > 1$. Equivalently, give an explicit construction of graphs on $n$ vertices which contain no clique and no independent set of size $\geq c \log n$, for some constant $c > 0$. We formalise "explicit" as: the adjacency relation of the graph on $n$ vertices is decided by a single algorithm that runs in time polynomial in $n$ (see `explicitGraph`). This is the weakest reasonable notion ("weakly explicit"); even this is open. The strongly explicit version, with time polynomial in $\log n$, is `erdos_78.variants.strongly_explicit`. This problem is #4 in Ramsey Theory in the graphs problem collection.
- notes: Erdos Problem 78 -- https://www.erdosproblems.com/78
- track: open
- answer_shape: proof
- source_stem: 78
- mathdb_ref: erdos:78
- source_namespace: Erdos78
- source_theorem: erdos_78
- source_category: research open
- source_ams: 5 68
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Real ComplexityTheory

namespace Problem

/--
The graph on `Fin n` described by an adjacency oracle `adj`. Two distinct vertices `u` and `v`
are adjacent if `adj (1ⁿ, u, v)` or `adj (1ⁿ, v, u)` is `true`.

The number of vertices is given in unary, as the list `List.replicate n true`. So if `adj` is
computable in polynomial time, then the whole graph on `n` vertices is computable in time
polynomial in `n`. This is the notion of a *weakly explicit* family of graphs; compare
`stronglyExplicitGraph`.
-/
def explicitGraph (adj : List Bool × ℕ × ℕ → Bool) (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v ↦ adj (List.replicate n true, u, v)

/--
The graph on `Fin n` described by an adjacency oracle `adj` which receives `n` in binary. Two
distinct vertices `u` and `v` are adjacent if `adj (n, u, v)` or `adj (n, v, u)` is `true`.

If `adj` is computable in polynomial time, then each adjacency query is answered in time
polynomial in $\log n$. This is the notion of a *strongly explicit* family of graphs, which is
what "explicit Ramsey graph" usually means in the literature (e.g. [Co15], [Li23b]). Compare
`explicitGraph`, where only time polynomial in $n$ is allowed.
-/
def stronglyExplicitGraph (adj : ℕ × ℕ × ℕ → Bool) (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v ↦ adj (n, u, v)

/--
The graph `G` has no clique and no independent set with `m` vertices.
-/
def NoHomogeneousSet {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  G.CliqueFree m ∧ Gᶜ.CliqueFree m

abbrev Target : Prop :=
    ∃ c > (0 : ℝ), ∃ adj : List Bool × ℕ × ℕ → Bool, IsPolyTime adj ∧
      ∀ᶠ n in atTop, NoHomogeneousSet (explicitGraph adj n) ⌈c * log n⌉₊

end Problem
