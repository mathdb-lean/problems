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

- problem_id: E191
- collection: erdos
- question_id: erdos:191
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/191.lean#erdos_191
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $C>0$ be arbitrary. Is it true that, if $n$ is sufficiently large depending on $C$, then in any $2$-colouring of $\binom{\{2,\ldots,n\}}{2}$ there exists some $X\subseteq \{2,\ldots,n\}$ such that $\binom{X}{2}$ is monochromatic and $$\sum_{x\in X}\frac{1}{\log x}\geq C?$$ The answer is yes, which was proved by Rödl [Ro03]. In the same article Rödl also proved a lower bound for this problem, constructing, for all $n$, a $2$-colouring of $\binom{\{2,\ldots,n\}}{2}$ such that if $X\subseteq \{2,\ldots,n\}$ is such that $\binom{X}{2}$ is monochromatic then $$\sum_{x\in X}\frac{1}{\log x}\ll \log\log\log n.$$ In the same paper Rödl proves that the answer to the main problem is negative if we consider $3$-colourings. This bound is best possible, as proved by Conlon, Fox, and Sudakov [CFS13], who proved that, if $n$ is sufficiently large, then in any $2$-colouring of $\binom{\{2,\ldots,n\}}{2}$ there exists some $X\subseteq \{2,\ldots,n\}$ such that $\binom{X}{2}$ is monochromatic and $$\sum_{x\in X}\frac{1}{\log x}\geq 2^{-8}\log\log\log n.$$ A $2$-colouring of the pairs of $\{2,\ldots,n\}$ is a graph `G` on this vertex set; a monochromatic set is a clique or an independent set of `G`.
- notes: Erdos Problem 191 -- https://www.erdosproblems.com/191
- track: solved
- answer_shape: decide
- source_stem: 191
- mathdb_ref: erdos:191
- source_namespace: Erdos191
- source_theorem: erdos_191
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ C : ℝ, 0 < C → ∀ᶠ n : ℕ in atTop,
        ∀ G : SimpleGraph (Finset.Icc 2 n), ∃ X : Finset (Finset.Icc 2 n),
          (G.IsClique X ∨ G.IsIndepSet X) ∧ C ≤ ∑ x ∈ X, 1 / Real.log (x : ℕ)

end Problem
