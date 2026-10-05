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

- problem_id: E1062_parts_ii_refute
- collection: erdos
- question_id: erdos:1062
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1062.lean#erdos_1062.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Erdős asked whether the limiting density `f n / n` exists and, if so, whether it is irrational.
- notes: Erdos Problem 1062 -- https://www.erdosproblems.com/1062
- track: open
- answer_shape: refute
- pair_id: E1062_parts_ii
- pair_role: refute
- source_stem: 1062
- mathdb_ref: erdos:1062
- source_namespace: Erdos1062
- source_theorem: erdos_1062.parts.ii
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter
open scoped Topology

namespace Problem

/-- A set `A` of positive integers is fork-free if no element divides two distinct
other elements of `A`. -/
def ForkFree (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ({b | b ∈ A \ {a} ∧ a ∣ b} : Set ℕ).Subsingleton

/-- The extremal function from Erdős problem 1062: the largest size of a fork-free subset of
`{1,...,n}`. -/
noncomputable def f (n : ℕ) : ℕ :=
  open scoped Classical in
  Nat.findGreatest (fun k => ∃ A ⊆ Set.Icc 1 n, ForkFree A ∧ A.ncard = k) n

abbrev Target : Prop :=
    ¬ (
      (∃ l, Tendsto (fun n => (f n : ℝ) / n) atTop (𝓝 l) ∧ Irrational l)
    )

end Problem
