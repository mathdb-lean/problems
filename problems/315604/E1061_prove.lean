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

- problem_id: E1061_prove
- collection: erdos
- question_id: erdos:1061
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1061.lean#erdos_1061
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: How many (ordered) solutions are there to `σ(a) + σ(b) = σ(a + b)` with `a + b ≤ x`? Is it true that this number is asymptotic to `c * x` for some constant `c > 0`?
- notes: Erdos Problem 1061 -- https://www.erdosproblems.com/1061
- track: open
- answer_shape: prove
- pair_id: E1061
- pair_role: prove
- source_stem: 1061
- mathdb_ref: erdos:1061
- source_namespace: Erdos1061
- source_theorem: erdos_1061
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Asymptotics
open scoped ArithmeticFunction.sigma

namespace Problem

/-- Let `S x` count the number of **ordered** pairs of positive integers `(a, b)` with `a + b ≤ x`
such that `σ(a) + σ(b) = σ(a + b)`, where `σ` is the sum of divisors function.

In particular, `(a, b)` and `(b, a)` are counted separately; an unordered variant could be obtained
by additionally requiring `a ≤ b`. -/
noncomputable abbrev S (x : ℝ) : ℝ :=
  ((Finset.Icc 1 ⌊x⌋₊ ×ˢ Finset.Icc 1 ⌊x⌋₊).filter fun (a, b) ↦
      a + b ≤ x ∧ σ 1 a + σ 1 b = σ 1 (a + b)).card

abbrev Target : Prop :=
    ∃ c : ℝ, 0 < c ∧ S ~[atTop] (fun x : ℝ ↦ c * x)

end Problem
