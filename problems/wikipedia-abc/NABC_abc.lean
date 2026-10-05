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

- problem_id: NABC_abc
- collection: wikipedia
- question_id: wikipedia:ABC
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/ABC.lean#abc
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: For every positive real number `ε`, there exist only finitely many triples `(a, b, c)` of coprime positive integers, with `a + b = c`, such that `c > rad(abc)^(1+ε)`
- notes: Wikipedia: ABC -- https://en.wikipedia.org/wiki/Abc_conjecture
- track: open
- answer_shape: proof
- source_stem: ABC
- source_namespace: ABC
- source_theorem: abc
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: radical_16 radical_17 radical_12
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
The radical of `n` denoted is the product of the distinct prime factors of `n`.
-/
def radical (n : ℕ) : ℕ := n.primeFactors.prod id

/--
Quality `q(a, b, c)` of the triple `(a, b, c)` is defined as `q(a,b,c) = log (c) / log (rad(abc))`.
-/
noncomputable def quality (a b c : ℕ) : ℝ := (c : ℝ).log / (radical <| a * b * c : ℝ).log

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem radical_16 : radical 16 = 2 := by
  have : Nat.primeFactors 16 = {2} := by
    rw [show 16 = 2 ^ 4 by decide, Nat.primeFactors_pow]
    · norm_num
    · decide
  norm_num [radical, this]

@[category test, AMS 11]
theorem radical_17 : radical 17 = 17 := by
  rw [radical, Nat.Prime.primeFactors (by norm_num), Finset.prod_singleton, id]

@[category test, AMS 11]
theorem radical_12 : radical 12 = 6 := by
  rw [radical, show 12 = 2^2 * 3 by rfl, Nat.primeFactors_mul (by norm_num)
    (by norm_num), Nat.primeFactors_pow _ (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
  rfl

abbrev Target : Prop :=
    ∀ (ε : ℝ) (hε : 0 < ε),
      {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧
      a + b = c ∧ (radical <| a * b * c : ℝ)^(1 + ε) < c}.Finite

end Problem
