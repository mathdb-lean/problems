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

- problem_id: E884
- collection: erdos
- question_id: erdos:884
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/884.lean#erdos_884
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: For a natural number n, let $1 = d_1 < \dotsc < d_{\tau(n)} = n$ denote the divisors of $n$ in increasing order. Does it hold that $\sum_{1 \le i < j \le \tau(n)} \frac{1}{d_j - d_i} \ll 1 + \sum_{1 \le i < \tau(n)} \frac{1}{d_{i + 1} - d_i}$ for $n \to \infty$, i.e. $\sum_{1 \le i < j \le \tau(n)} \frac{1}{d_j - d_i} \in O \left( 1 + \sum_{1 \le i < \tau(n)} \frac{1}{d_{i + 1} - d_i} \right)$? This conjecture has been **disproved**: - In September 2025, Terence Tao gave a conditional _negative_ answer assuming the prime tuples conjecture, see `erdos_884_false_of_hardy_littlewood` for this implication. - Daniel Larsen subsequently gave an [unconditional disproof](https://github.com/Larsen-Daniel/Erdos-884/blob/main/884.pdf). *Reference:* [erdosproblems.com/884](https://www.erdosproblems.com/884)
- notes: Erdos Problem 884 -- https://www.erdosproblems.com/884
- track: solved
- answer_shape: decide
- source_stem: 884
- mathdb_ref: erdos:884
- source_namespace: Erdos884
- source_theorem: erdos_884
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

/--
The sum $\sum_{1 \le i < j \le \tau(n)} \frac{1}{d_j - d_i}$ over all pairs of
divisors $d_i < d_j$ of $n$.
-/
noncomputable abbrev sumDivisorInvPairwiseDifference (n : ℕ) : ℝ :=
    ∑ j : Fin n.divisors.card, ∑ i : Fin  j,
    (1 : ℚ) / (Nat.nth (· ∣ n) j - Nat.nth (· ∣ n) i )

/--
The sum $\sum_{1 \le i < \tau(n)} \frac{1}{d_{i + 1} - d_i}$ over consecutive
divisors of $n$.
-/
noncomputable abbrev sumDivisorInvConsecutiveDifference (n : ℕ) : ℝ :=
    ∑ i : Fin (n.divisors.card - 1),
    (1 : ℚ) / (Nat.nth (· ∣ n) (i + 1) - Nat.nth (· ∣ n) i)

/--
For a natural number n, let $1 = d_1 < \dotsc < d_{\tau(n)} = n$ denote the divisors of $n$
in increasing order.
Does it hold that
$\sum_{1 \le i < j \le \tau(n)} \frac{1}{d_j - d_i} \ll 1 + \sum_{1 \le i < \tau(n)}
 \frac{1}{d_{i + 1} - d_i}$
for $n \to \infty$, i.e.
$\sum_{1 \le i < j \le \tau(n)} \frac{1}{d_j - d_i} \in O \left( 1 + \sum_{1 \le i < \tau(n)}
 \frac{1}{d_{i + 1} - d_i} \right)$?

This conjecture has been **disproved**:
- In September 2025, Terence Tao gave a conditional _negative_ answer assuming the prime tuples
  conjecture, see `erdos_884_false_of_hardy_littlewood` for this implication.
- Daniel Larsen subsequently gave an unconditional disproof.
-/
def Erdos884Prop : Prop :=
    sumDivisorInvPairwiseDifference ≪ 1 + sumDivisorInvConsecutiveDifference

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ Erdos884Prop

end Problem
