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

- problem_id: E698
- collection: erdos
- question_id: erdos:698
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/698.lean#erdos_698
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is there some $h(n)\to \infty$ such that for all $2\leq i<j\leq n/2$ $$\textrm{gcd}\left( \binom{n}{i},\binom{n}{j}\right) \geq h(n)?$$ This was resolved by Bergman [Be11], who proved that for any $2\leq i<j\leq n/2$ $$\textrm{gcd}\left( \binom{n}{i},\binom{n}{j}\right) \gg n^{1/2}\frac{2^i}{i^{3/2}},$$ where the implied constant is absolute. The linked formal proof (van Doorn and Aristotle, see `erdos_698.variants.bergman`) gives the explicit bound $\gcd > \frac{2^i \sqrt n}{4 i \sqrt{i - 1}}$, so $h(n) = \lfloor \sqrt n / 4 \rfloor$ works since $i \sqrt{i - 1} \le 2^i$ for $i \ge 2$.
- notes: Erdos Problem 698 -- https://www.erdosproblems.com/698
- track: solved
- answer_shape: decide
- source_stem: 698
- mathdb_ref: erdos:698
- source_namespace: Erdos698
- source_theorem: erdos_698
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

open Filter

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ h : ℕ → ℕ, Tendsto h atTop atTop ∧
          ∀ n i j : ℕ, 2 ≤ i → i < j → j ≤ n / 2 →
            h n ≤ Nat.gcd (n.choose i) (n.choose j)

end Problem
