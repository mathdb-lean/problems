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

- problem_id: E753
- collection: erdos
- question_id: erdos:753
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/753.lean#erdos_753
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: The list chromatic number $\chi_L(G)$ is defined to be the minimal $k$ such that for any assignment of a list of $k$ colours to each vertex of $G$ (perhaps different lists for different vertices) a colouring of each vertex by a colour on its list can be chosen such that adjacent vertices receive distinct colours. Does there exist some constant $c>0$ such that $$\chi_L(G)+\chi_L(G^c)> n^{1/2+c}$$ for every graph $G$ on $n$ vertices (where $G^c$ is the complement of $G$)? A problem of Erdős, Rubin, and Taylor. The answer is no: Alon [Al92] proved that, for every $n$, there exists a graph $G$ on $n$ vertices such that $$\chi_L(G)+\chi_L(G^c)\ll (n\log n)^{1/2},$$ where the implied constant is absolute.
- notes: Erdos Problem 753 -- https://www.erdosproblems.com/753
- track: solved
- answer_shape: decide
- source_stem: 753
- mathdb_ref: erdos:753
- source_namespace: Erdos753
- source_theorem: erdos_753
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

/--
A graph $G$ is $k$-choosable if for any assignment of a list of $k$ colours to each vertex of $G$
(perhaps different lists for different vertices) a colouring of each vertex by a colour on its list
can be chosen such that adjacent vertices receive distinct colours.
-/
def IsKChoosable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, (L v).card = k) → ∃ C : G.Coloring ℕ, ∀ v, C v ∈ L v

/--
The list chromatic number $\chi_L(G)$, defined to be the minimal $k$ such that $G$ is
$k$-choosable.
-/
noncomputable def listChromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | IsKChoosable G k}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → ∀ G : SimpleGraph (Fin n),
          (n : ℝ) ^ ((1 : ℝ) / 2 + c) <
            (listChromaticNumber G : ℝ) + (listChromaticNumber Gᶜ : ℝ)

end Problem
