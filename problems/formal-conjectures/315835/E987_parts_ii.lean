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

- problem_id: E987_parts_ii
- collection: erdos
- question_id: erdos:987
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/987.lean#erdos_987.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Question 2 (parts.ii)**: Is it possible for $A_k = o(k)$? Yes — there exists a sequence $(x_n) \in (0, 1)$ and a bound $b(k) = o(k)$ with $A x k \le b k$ eventually. A corollary of `sqrt_log_upper_bound` (which gives a $\sqrt{k \log k}$ bound) plus the asymptotic $\sqrt{k \log k} = o(k)$.
- notes: Erdos Problem 987 -- https://www.erdosproblems.com/987
- track: solved
- answer_shape: decide
- source_stem: 987
- mathdb_ref: erdos:987
- source_namespace: Erdos987
- source_theorem: erdos_987.parts.ii
- source_category: research solved
- source_ams: 11 40 42
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Finset Asymptotics
open scoped ExponentialSum

namespace Problem

/-
Here we use 0-indexing for generality and convenience, while in the original problem
formulation 1-indexing was used. This change does not affect the meaning of the problem.
In the description of the problem below we remain faithful to the original one.
-/

/--
For an infinite sequence $x_1, x_2, \ldots \in (0, 1)$, define
$$A_k = \limsup_{n \to \infty} \left\lvert \sum_{j \le n} e(k x_j) \right\rvert,$$
where $e(x) = e^{2\pi i x}$.
-/
noncomputable def A (x : ℕ → ℝ) (k : ℕ) : EReal :=
  atTop.limsup fun n : ℕ => (‖∑ j ∈ range n, e (k * x j)‖ : EReal)

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ (x : ℕ → ℝ) (_ : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1) (b : ℕ → ℝ),
      b =o[atTop] (fun k : ℕ => (k : ℝ)) ∧ ∀ᶠ k : ℕ in atTop, A x k ≤ ((b k : ℝ) : EReal)

end Problem
