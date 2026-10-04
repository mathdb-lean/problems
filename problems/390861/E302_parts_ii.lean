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

- problem_id: E302_parts_ii
- collection: erdos
- question_id: erdos:302
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/302.lean#erdos_302.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: In particular, is $f(N)=(\tfrac{1}{2}+o(1))N$? This is false: it is contradicted by Cambie's lower bound of $(5/8+o(1))N$ recorded below, since $5/8 > 1/2$.
- notes: Erdos Problem 302 -- https://www.erdosproblems.com/302
- track: solved
- answer_shape: proof
- source_stem: 302
- mathdb_ref: erdos:302
- source_namespace: Erdos302
- source_theorem: erdos_302.parts.ii
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Finset
open scoped Topology

namespace Problem

/--
A finite set $A$ of positive integers admits no solution to
$\frac{1}{a} = \frac{1}{b} + \frac{1}{c}$ with $a, b, c$ distinct elements of $A$.
-/
def NoUnitFractionTriple (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → b ≠ c →
    (1 : ℚ) / a ≠ (1 : ℚ) / b + (1 : ℚ) / c

/--
$f N$ is the size of the largest $A ⊆ \{1, …, N\}$ containing no solution to
$\frac{1}{a} = \frac{1}{b} + \frac{1}{c}$ with distinct $a, b, c ∈ A$.
-/
def IsMaxNoTripleCard (N m : ℕ) : Prop :=
  IsGreatest {k | ∃ A ⊆ Finset.Icc 1 N, NoUnitFractionTriple A ∧ A.card = k} m

abbrev Target : Prop :=
    ∀ (f : ℕ → ℕ) (hf : ∀ N, IsMaxNoTripleCard N (f N)),
      ¬ Tendsto (fun N : ℕ => (f N : ℝ) / N) atTop (𝓝 ((1 : ℝ) / 2))

end Problem
