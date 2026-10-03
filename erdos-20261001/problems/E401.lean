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

- problem_id: E401
- collection: erdos
- question_id: erdos:401
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/401.lean#erdos_401
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is there some function $f(r)$ such that $f(r)\to \infty$ as $r\to\infty$, such that, for infinitely many $n$, there exist $a_1,a_2$ with $$a_1+a_2> n+f(r)\log n$$ such that $a_1!a_2! \mid n!2^n3^n\cdots p_r^n$? It is ambiguous in [ErGr80] what the intended quantifiers are on the variables (they write 'is it true that we can find $a_1+a_2>n+f(r)\log n$...'). Comparing to previous problems such as [728] and [729] it seems most likely that they intended to ask the formulation in the problem statement. The answer is yes: Barreto and Leeham have used ChatGPT to provide a proof of the stated problem (in fact essentially the same construction as their solution to [729]).
- notes: Erdos Problem 401 -- https://www.erdosproblems.com/401
- track: solved
- answer_shape: decide
- source_stem: 401
- mathdb_ref: erdos:401
- source_namespace: Erdos401
- source_theorem: erdos_401
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧
          ∀ (r : ℕ) (hr : 1 ≤ r),
            {n : ℕ | ∃ a₁ a₂ : ℕ, 0 < a₁ ∧ 0 < a₂ ∧
              (a₁ : ℝ) + a₂ > n + f r * Real.log n ∧
              a₁.factorial * a₂.factorial ∣
                n.factorial * (∏ i ∈ Finset.range r, Nat.nth Nat.Prime i) ^ n}.Infinite

end Problem
