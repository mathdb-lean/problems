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

- problem_id: E728
- collection: erdos
- question_id: erdos:728
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/728.lean#erdos_728
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $\varepsilon$ be sufficiently small and $C, C' > 0$. Are there integers $a, b, n$ such that $$a, b > \varepsilon n\quad a!\, b! \mid n!\, (a + b - n)!, $$ and $$C \log n < a + b - n < C' \log n ?$$ Note that the website currently displays a simpler (trivial) version of this problem because $a + b$ isn't assumed to be in the $n + O(\log n)$ regime. Barreto and ChatGPT-5.2 have proved that, for any $0 < C_1 < C_2$, there are infinitely many $a, b, n$ with $b = n/2$, $a = n/2 + O(\log n)$, and $C_1 \log n < a + b - n < C_2 \log n$ such that $a! b! \mid n! (a + b - n)!$ This appears to answer the question in the spirit it was intended. This was formalized in Lean by Alexeev using Aristotle.
- notes: Erdos Problem 728 -- https://www.erdosproblems.com/728
- track: solved
- answer_shape: decide
- source_stem: 728
- mathdb_ref: erdos:728
- source_namespace: Erdos728
- source_theorem: erdos_728
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Real
open scoped Nat Topology

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
      ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ C > (0 : ℝ), ∀ C' > C,
        ∃ a b n : ℕ,
          0 < n ∧
          ε * n < a ∧
          ε * n < b ∧
          a ! * b ! ∣ n ! * (a + b - n)! ∧
          a + b > n + C * log n ∧
          a + b < n + C' * log n

end Problem
