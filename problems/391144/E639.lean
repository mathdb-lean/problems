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

- problem_id: E639
- collection: erdos
- question_id: erdos:639
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/639.lean#erdos_639
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that if the edges of $K_n$ are 2-coloured then there are at most $n^2/4$ many edges which do not occur in a monochromatic triangle? Solved by Erdős, Rousseau, and Schelp for large $n$, but unpublished. Alon has observed that this also follows from a result of Pyber [Py86], which states that (for large enough $n$) at most $\lfloor n^2/4\rfloor+2$ monochromatic cliques cover all edges of a $2$-coloured $K_n$. This problem was solved completely by Keevash and Sudakov [KeSu04], who proved that the correct threshold is $\lfloor n^2/4\rfloor$ for all $n\geq 7$, is $\binom{n}{2}$ for $n\leq 5$, and is $10$ for $n=6$. Since the bound fails for small $n$ (at $n=6$ the threshold is $10 > 6^2/4$), the statement is formalized in the asymptotic reading in which the problem was posed and solved: for all sufficiently large $n$, every $2$-colouring of the edges of $K_n$ leaves at most $n^2/4$ edges not occurring in a monochromatic triangle. Edges of $K_n$ are the non-diagonal unordered pairs `Sym2 (Fin n)`; an edge $\{x, y\}$ occurs in a monochromatic triangle if and only if there is a third vertex $z$ with $C(\{x, z\}) = C(\{y, z\}) = C(\{x, y\})$. The linked file proves the bound for every finite vertex type with at least $10$ vertices, which gives the `atTop` reading below, and collects the uncovered edges as the edge set of a graph rather than as a set of pairs.
- notes: Erdos Problem 639 -- https://www.erdosproblems.com/639
- track: solved
- answer_shape: decide
- source_stem: 639
- mathdb_ref: erdos:639
- source_namespace: Erdos639
- source_theorem: erdos_639
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
    verdict ↔
        ∀ᶠ (n : ℕ) in atTop, ∀ C : Sym2 (Fin n) → Fin 2,
          {e : Sym2 (Fin n) | ¬e.IsDiag ∧
            ∀ x y : Fin n, e = s(x, y) →
              ¬∃ z, z ≠ x ∧ z ≠ y ∧ C s(x, z) = C e ∧ C s(y, z) = C e}.ncard ≤ n ^ 2 / 4

end Problem
