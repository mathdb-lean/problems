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

- problem_id: E997
- collection: erdos
- question_id: erdos:997
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/997.lean#erdos_997
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that, for every $\alpha$, the sequence $\{ \alpha p_n\}$ is not well-distributed, if $p_n$ is the sequence of primes? The answer is yes, by [APSSV26, Section 4]; a Lean formalisation is available in [Mo26].
- notes: Erdos Problem 997 -- https://www.erdosproblems.com/997
- track: solved
- answer_shape: decide
- source_stem: 997
- mathdb_ref: erdos:997
- source_namespace: Erdos997
- source_theorem: erdos_997
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Set

namespace Problem

/--
Call $x_1,x_2,\ldots \in (0,1)$ well-distributed if, for every $\epsilon>0$, if $k$ is
sufficiently large then, for all $n>0$ and intervals $I\subseteq [0,1]$,
$\lvert \# \{ n < m\leq n+k : x_m\in I\} - \lvert I\rvert k\rvert < \epsilon k.$

The notion of a well-distributed sequence was introduced by Hlawka and Petersen [Hl55].
-/
def IsWellDistributed (x : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ k in Filter.atTop, ∀ n : ℕ,
  ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 →
    letI I := Ico a b
    let count := (Finset.Ioc n (n + k)).filter (fun m ↦ x m ∈ I)
    abs ((count.card : ℝ) - (b - a) * k) < ε * k

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
      ∀ α : ℝ, ¬ IsWellDistributed (fun n ↦ Int.fract (α * (n.nth Nat.Prime)))

end Problem
