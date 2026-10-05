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

- problem_id: E563
- collection: erdos
- question_id: erdos:563
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/563.lean#erdos_563
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $F(n,\alpha)$ denote the smallest $m$ such that there exists a $2$-colouring of the edges of $K_n$ so that every $X\subseteq [n]$ with $\lvert X\rvert\geq m$ contains more than $\alpha \binom{\lvert X\rvert}{2}$ many edges of each colour. Prove that, for every $0\leq \alpha < 1/2$, $$F(n,\alpha)\sim c_\alpha\log n$$ for some constant $c_\alpha$ depending only on $\alpha$. This problem is #39 in Ramsey Theory in the graphs problem collection.
- notes: Erdos Problem 563 -- https://www.erdosproblems.com/563
- track: open
- answer_shape: proof
- source_stem: 563
- mathdb_ref: erdos:563
- source_namespace: Erdos563
- source_theorem: erdos_563
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter

namespace Problem

open scoped Classical in
/--
A 2-coloring of $K_n$ (represented by graph $G$ on $\mathrm{Fin}\; n$) is balanced on subsets
of size at least $m$ with parameter $\alpha$ if every $X \subseteq [n]$ with $|X| \geq m$
contains more than $\alpha \binom{|X|}{2}$ edges of each color.
-/
def HasBalancedSubsets (n : ℕ) (m : ℕ) (α : ℝ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ (X : Finset (Fin n)), m ≤ X.card →
    α * (X.card.choose 2 : ℝ) < ((G.induce (X : Set (Fin n))).edgeFinset.card : ℝ) ∧
    ((G.induce (X : Set (Fin n))).edgeFinset.card : ℝ) < (1 - α) * (X.card.choose 2 : ℝ)

open scoped Classical in
/--
$F(n,\alpha)$ is the smallest $m$ such that there exists a 2-coloring of the edges of $K_n$
so that every $X\subseteq [n]$ with $|X|\geq m$ contains more than $\alpha\binom{|X|}{2}$
edges of each color.
-/
noncomputable def F (n : ℕ) (α : ℝ) : ℕ :=
  sInf {m | ∃ (G : SimpleGraph (Fin n)), HasBalancedSubsets n m α G}

abbrev Target : Prop :=
    ∀ (α : ℝ), 0 ≤ α → α < 1 / 2 →
      ∃ (c : ℝ), 0 < c ∧
        Tendsto (fun n : ℕ => (F n α : ℝ) / Real.log n) atTop (nhds c)

end Problem
