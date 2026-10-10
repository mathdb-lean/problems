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

- problem_id: E445_prove
- collection: erdos
- question_id: erdos:445
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/445.lean#erdos_445
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that, for any $c>1/2$, if $p$ is a sufficiently large prime then, for any $n\geq 0$, there exist $a,b\in(n,n+p^c)$ such that $ab\equiv 1\pmod{p}$? This is discussed in this MathOverflow question [MathOverflow].
- notes: Erdos Problem 445 -- https://www.erdosproblems.com/445
- track: open
- answer_shape: prove
- pair_id: E445
- pair_role: prove
- source_stem: 445
- mathdb_ref: erdos:445
- source_namespace: Erdos445
- source_theorem: erdos_445
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter

namespace Problem

/--
The property that there exist $a,b\in(n,n+p^c)$ such that $ab\equiv 1\pmod{p}$.
-/
def Erdos445Prop (c : ℝ) (p n : ℕ) : Prop :=
  ∃ a b : ℕ,
    n < a ∧ (a : ℝ) < (n : ℝ) + (p : ℝ) ^ c ∧
    n < b ∧ (b : ℝ) < (n : ℝ) + (p : ℝ) ^ c ∧
    a * b ≡ 1 [MOD p]

abbrev Target : Prop :=
    ∀ c : ℝ, c > 1 / 2 →
      ∀ᶠ p : ℕ in atTop, p.Prime → ∀ n : ℕ, Erdos445Prop c p n

end Problem
