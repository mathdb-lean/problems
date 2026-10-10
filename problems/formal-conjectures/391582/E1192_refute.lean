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

- problem_id: E1192_refute
- collection: erdos
- question_id: erdos:1192
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1192.lean#erdos_1192
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does there exist, for all $r\geq 2$, a basis $A$ of order $r$ (so that $f_r(n)>0$ for all large $n$) such that $$\sum_{n\leq x}f_r(n)^2 \ll x$$ for all $x$?
- notes: Erdos Problem 1192 -- https://www.erdosproblems.com/1192
- track: open
- answer_shape: refute
- pair_id: E1192
- pair_role: refute
- source_stem: 1192
- mathdb_ref: erdos:1192
- source_namespace: Erdos1192
- source_theorem: erdos_1192
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Nat Filter Finset Set
open scoped Asymptotics BigOperators

namespace Problem

/--
For $A\subset \mathbb{N}$ let $f_r(n)$ count the number of solutions to $n=a_1+\cdots+a_r$
with $a_i\in A$.
-/
noncomputable def f_r (A : Set ℕ) (r n : ℕ) : ℕ :=
  { v : Fin r → ℕ | (∀ i, v i ∈ A) ∧ ∑ i, v i = n }.ncard

abbrev Target : Prop :=
    ¬ (
      ∀ r ≥ 2, ∃ A : Set ℕ,
          (∀ᶠ n in atTop, f_r A r n > 0) ∧
          (fun (x : ℕ) ↦ ∑ n ∈ range (x + 1), (f_r A r n : ℝ) ^ 2) =O[atTop]
            (fun (x : ℕ) ↦ (x : ℝ))
    )

end Problem
