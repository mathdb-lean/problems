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

- problem_id: NBoundedBurnsideProblem_bounded_burnside_problem
- collection: wikipedia
- question_id: wikipedia:BoundedBurnsideProblem
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/BoundedBurnsideProblem.lean#bounded_burnside_problem
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $G$ be a finitely generated group, and assume there exists $n$ such that for every $g$ in $G$, $g^n = 1$. Must $G$ be finite? The answer is negative. Novikov and Adian proved that for every odd $n > 4381$ there exist infinite, finitely generated groups of exponent $n$ [NA68]; Adian later reduced this to odd $n > 665$ [Ad79]. The even case is harder: Ivanov proved $B(m, n)$ infinite for $m > 1$ and even $n \ge 2^{48}$ divisible by $2^9$ [Iv94], and Lysënok improved this to $m > 1$ and $n \ge 8000$ [Ly96]. Any such group, for example the free Burnside group $B(2, 667)$, refutes the statement below. Note this concerns only the universally quantified question stated here, which a single counterexample closes. The classification of which free Burnside groups $B(m, n)$ are finite remains open, with $B(2, 5)$ the best known open case.
- notes: Wikipedia: BoundedBurnsideProblem -- https://en.wikipedia.org/wiki/Burnside_problem#Bounded_Burnside_problem
- track: solved
- answer_shape: decide
- source_stem: BoundedBurnsideProblem
- source_namespace: BoundedBurnsideProblem
- source_theorem: bounded_burnside_problem
- source_category: research solved
- source_ams: 20
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ (G : Type) [Group G] (fin_gen : Group.FG G)
      (n : ℕ) (hn : n > 0) (bounded : ∀ g : G, g^n = 1), Finite G

end Problem
