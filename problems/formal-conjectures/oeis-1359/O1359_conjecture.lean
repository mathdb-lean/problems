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

- problem_id: O1359_conjecture
- collection: oeis
- question_id: oeis:1359
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/1359.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Primes $p_k$ such that $p_k! \equiv 1 \pmod{p_{k+1}}$ with the exception of $p_{991} = 7841$ and other unknown primes $p_k$ for which $(p_k+1)(p_k+2)\cdots(p_{k+1}-2) \equiv 1 \pmod{p_{k+1}}$ where $p_{k+1} - p_k > 2$. A formal proof is hosted at the `formal_proof` link: a Wilson-theorem argument with a fixed-divisor trial-division sieve and a verified length-7840 certificate.
- notes: OEIS A1359 -- https://oeis.org/A1359
- track: solved
- answer_shape: proof
- source_stem: 1359
- source_namespace: OeisA1359
- source_theorem: conjecture
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- The $n$-th lesser twin prime, with $a(0) = 0$. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n > 0 then
    Nat.nth (fun p => p.Prime ∧ (p + 2).Prime) (n - 1)
  else
    0

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 3 := by
  norm_num[a]
  exact(((congr_arg _) (by constructor) )).trans.comp (3).nth_count (by decide)

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 5 := by
  delta a
  apply((congr_arg _) (by constructor) ).trans (Nat.nth_count (by decide ) )

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 11 := by
  (inhabit ℝ)
  norm_num[a]
  exact (congr_arg _ (by decide)).trans (Nat.nth_count (by decide))

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 17 := by
  simp_all[a]
  exact (congr_arg _ (by constructor) ).trans (Nat.nth_count (by decide))

abbrev Target : Prop :=
    ∀ (k : ℕ) (hk : k > 1),
      let Pk := Nat.nth Nat.Prime (k - 1)
      let Pk_succ := Nat.nth Nat.Prime k
      let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
      let IsLesserTwinPrime := (Pk + 2).Prime
      let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
      Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))

end Problem
