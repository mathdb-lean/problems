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

- problem_id: E729
- collection: erdos
- question_id: erdos:729
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/729.lean#erdos_729
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $C>0$ be a constant. Are there infinitely many integers $a,b,n$ with $a+b> n+C\log n$ such that the denominator of $$\frac{n!}{a!b!}$$contains only primes $\ll_C 1$? Erdős [Er68c] proved that if $a!b!\mid n!$ then $a+b\leq n+O(\log n)$. This has been proved in the affirmative by Barreto and Leeham, using ChatGPT and Aristotle, with a modification of the argument used for [728].
- notes: Erdos Problem 729 -- https://www.erdosproblems.com/729
- track: solved
- answer_shape: decide
- source_stem: 729
- mathdb_ref: erdos:729
- source_namespace: Erdos729
- source_theorem: erdos_729
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ (C : ℝ) (hC : C > 0),
      ∃ K ≥ 3, Set.Infinite { T : ℕ × ℕ × ℕ |
        let (a, b, n) := T
        a > 0 ∧ b > 0 ∧ n > 0 ∧
        (a : ℝ) + b > n + C * Real.log n ∧
        ∀ p, p.Prime → p > K →
          padicValNat p ((n.factorial / (a.factorial * b.factorial) : ℚ).den) = 0 }

end Problem
