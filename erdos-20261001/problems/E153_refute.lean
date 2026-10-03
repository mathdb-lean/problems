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

- problem_id: E153_refute
- collection: erdos
- question_id: erdos:153
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/153.lean#erdos_153
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A$ be a finite Sidon set and $A+A=\{s_1<\cdots<s_t\}$. Is it true that $$\frac{1}{t}\sum_{1\leq i<t}(s_{i+1}-s_i)^2 \to \infty$$ as $\lvert A\rvert\to \infty$?
- notes: Erdos Problem 153 -- https://www.erdosproblems.com/153
- track: open
- answer_shape: refute
- pair_id: E153
- pair_role: refute
- source_stem: 153
- mathdb_ref: erdos:153
- source_namespace: Erdos153
- source_theorem: erdos_153
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open scoped Pointwise
open Filter Finset Nat

namespace Problem

/-- Define $f(n)$ to be the minimum of
$\frac{1}{t}\sum_{1\leq i<t}(s_{i+1}-s_i)^2$ as $A$ ranges over all Sidon sets of size $n$, where
$A+A=\{s_1<\cdots<s_t\}$. -/
noncomputable def f (n : ℕ) : ℝ := ⨅ A : {A : Finset ℕ | A.card = n ∧ IsSidon (A : Set ℕ)},
  let s := (A.1 + A).orderIsoOfFin rfl
  (∑ i : Set.Ico 1 ((A.1 + A).card), (s ⟨i, i.2.2⟩ - s ⟨i - 1, by grind⟩) ^ 2 : ℝ) / ((A.1 + A).card : ℝ)

abbrev Target : Prop :=
    ¬ (
      Tendsto f atTop atTop
    )

end Problem
