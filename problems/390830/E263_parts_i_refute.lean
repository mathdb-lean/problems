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

- problem_id: E263_parts_i_refute
- collection: erdos
- question_id: erdos:263
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/263.lean#erdos_263.parts.i
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is $a_n = 2^{2^n}$ an irrationality sequence in the above sense?
- notes: Erdos Problem 263 -- https://www.erdosproblems.com/263
- track: open
- answer_shape: refute
- pair_id: E263_parts_i
- pair_role: refute
- source_stem: 263
- mathdb_ref: erdos:263
- source_namespace: Erdos263
- source_theorem: erdos_263.parts.i
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter
open scoped Topology

namespace Problem

/--
We call a **strictly increasing** sequence $a_n$ of positive integers an
_irrationality sequence_ if for any sequence $b_n$ of positive integers with
$\frac{a_n}{b_n} \to 1$ as $n \to \infty$,
the sum $\sum \frac{1}{b_n}$ converges to an irrational number.

Note: erdosproblems.com/263 was corrected on 2026-04-02 to require the sequence
to be increasing; the pre-correction statement (no monotonicity hypothesis) had a
counterexample to Q2 that is not increasing (see `erdos_263.parts.ii` below).

Note: This is one of many possible notions of "irrationality sequences". See
FormalConjectures/ErdosProblems/264.lean for another possible definition.
-/
def IsIrrationalitySequence (a : ℕ → ℕ) : Prop :=
  (∀ n : ℕ, a n > 0) ∧
    StrictMono a ∧
    (∀ b : ℕ → ℕ, (∀ n : ℕ, b n > 0) ∧
      atTop.Tendsto (fun n : ℕ => (a n : ℝ) / (b n : ℝ)) (𝓝 1) →
      Irrational (∑' n, 1 / (b n : ℝ)))

/-- The nondecreasing version of `IsIrrationalitySequence`, as used by Koizumi [Ko25]: the sequence
is positive and nondecreasing, and every positive sequence asymptotic to it has irrational
reciprocal sum. -/
def IsWeakIrrationalitySequence (a : ℕ → ℕ) : Prop :=
  (∀ n : ℕ, a n > 0) ∧
    Monotone a ∧
    (∀ b : ℕ → ℕ, (∀ n : ℕ, b n > 0) ∧
      atTop.Tendsto (fun n : ℕ => (a n : ℝ) / (b n : ℝ)) (𝓝 1) →
      Irrational (∑' n, 1 / (b n : ℝ)))

abbrev Target : Prop :=
    ¬ (
      IsIrrationalitySequence (fun n : ℕ => 2 ^ 2 ^ n)
    )

end Problem
