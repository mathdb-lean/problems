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

- problem_id: E894
- collection: erdos
- question_id: erdos:894
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/894.lean#erdos_894
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A=\{n_1<n_2<\cdots\}\subset \mathbb{N}$ be a lacunary sequence (so there exists some $\epsilon>0$ with $n_{k+1}\geq (1+\epsilon)n_k$ for all $k$). Is it true that there must exist a finite colouring of $\mathbb{N}$ with no monochromatic solutions to $a-b\in A$? Asked by Erdős in 1987, according to Katznelson [Ka01]. In other words, does the Cayley graph defined on $\mathbb{Z}$ by a lacunary sequence have a finite chromatic number? Katznelson observed that a positive solution to the problem follows from the answer to [464](https://www.erdosproblems.com/464), which yields an irrational $\theta$ and $\delta>0$ such that $\inf_k \| \theta n_k\|>\delta$. In particular, the solution to [464](https://www.erdosproblems.com/464) implies the answer to this question is yes, with the best known quantitative bound, due to Peres and Schlag [PeSc10], being that there is a colouring with no solutions using at most $\ll \epsilon^{-1}\log(1/\epsilon)$ colours.
- notes: Erdos Problem 894 -- https://www.erdosproblems.com/894
- track: solved
- answer_shape: decide
- source_stem: 894
- mathdb_ref: erdos:894
- source_namespace: Erdos894
- source_theorem: erdos_894
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ n : ℕ → ℕ, StrictMono n → (∀ k, 0 < n k) → IsLacunary n →
          ∃ (r : ℕ) (c : ℕ → Fin r), ∀ b k, c (b + n k) ≠ c b

end Problem

/- Formalization note: as in `erdos_464`, the lacunarity hypothesis is rendered by the house
predicate `IsLacunary` ($\exists c > 1$ with $c \cdot n_k < n_{k+1}$ for all sufficiently large
$k$); for a strictly increasing sequence of positive integers this is equivalent to the problem's
condition $n_{k+1} \geq (1+\epsilon) n_k$ for all $k$. -/
