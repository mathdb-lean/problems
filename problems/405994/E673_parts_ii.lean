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

- problem_id: E673_parts_ii
- collection: erdos
- question_id: erdos:673
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/673.lean#erdos_673.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Can one prove an asymptotic formula for $\sum_{n\leq X}G(n)$? Indeed $\sum_{n\leq X}G(n)\sim X\log X$.
- notes: Erdos Problem 673 -- https://www.erdosproblems.com/673
- track: solved
- answer_shape: proof
- source_stem: 673
- mathdb_ref: erdos:673
- source_namespace: Erdos673
- source_theorem: erdos_673.parts.ii
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Asymptotics Real

namespace Problem

/-- If $1=d_1<\cdots <d_{\tau(n)}=n$ are the divisors of $n$ (here `Nat.nth (· ∣ n) i` is
$d_{i+1}$), then
$$G(n) = \sum_{1\leq i<\tau(n)}\frac{d_i}{d_{i+1}}.$$ -/
noncomputable def G (n : ℕ) : ℝ :=
  ∑ i : Fin (n.divisors.card - 1), (Nat.nth (· ∣ n) i : ℝ) / Nat.nth (· ∣ n) (i + 1)

abbrev Target : Prop :=
    (fun X : ℕ ↦ ∑ n ∈ Finset.Icc 1 X, G n) ~[atTop] fun X : ℕ ↦ (X : ℝ) * log X

end Problem
