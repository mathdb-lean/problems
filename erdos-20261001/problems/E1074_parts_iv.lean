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

- problem_id: E1074_parts_iv
- collection: erdos
- question_id: erdos:1074
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1074.lean#erdos_1074.parts.iv
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Similarly, if $P$ is the set of all primes $p$ such that there exists an $m$ with $p\not\equiv 1\pmod{m}$ such that $m! + 1 \equiv 0\pmod{p}$, then what is $$ \lim\frac{|P\cap[1, x]|}{\pi(x)}? $$
- notes: Erdos Problem 1074 -- https://www.erdosproblems.com/1074
- track: open
- answer_shape: value
- answer_type: ℝ
- answer_pinned: true
- answer_pinned_reason: density_is_unique
- source_stem: 1074
- mathdb_ref: erdos:1074
- source_namespace: Erdos1074
- source_theorem: erdos_1074.parts.iv
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: two_not_mem_pillaiPrimes twentyThree_mem_pillaiPrimes
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open scoped Nat
open Nat

/-- The EHS numbers (after Erdős, Hardy, and Subbarao) are those $m\geq 1$ such that there
exists a prime $p\not\equiv 1\pmod{m}$ such that $m! + 1 \equiv 0\pmod{p}$. -/
abbrev EHSNumbers : Set ℕ := {m | 1 ≤ m ∧ ∃ p, p.Prime ∧ ¬p ≡ 1 [MOD m] ∧ p ∣ m ! + 1}

/-- The Pillai primes are those primes $p$ such that there exists an $m \ge 1$ with
$p\not\equiv 1\pmod{m}$ such that $m! + 1 \equiv 0\pmod{p}$-/
abbrev PillaiPrimes : Set ℕ := {p | p.Prime ∧ ∃ m ≥ 1, ¬p ≡ 1 [MOD m] ∧ p ∣ m ! + 1}

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem two_not_mem_pillaiPrimes : ¬ 2 ∈ PillaiPrimes := by
  norm_num
  intro m hm h
  exact (Nat.dvd_factorial (by decide) (hm.lt_of_ne (by bound))).modEq_zero_nat.add_right 1

@[category test, AMS 11]
theorem twentyThree_mem_pillaiPrimes : 23 ∈ PillaiPrimes := by
  norm_num
  use 14
  decide

abbrev Target (value : ℝ) : Prop :=
    PillaiPrimes.HasDensity value {p | p.Prime}

end Problem
