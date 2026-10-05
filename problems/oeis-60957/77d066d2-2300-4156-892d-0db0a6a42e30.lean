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

- problem_id: O60957_conjecture
- collection: oeis
- question_id: oeis:60957
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/60957.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture: let $p \le n$ be prime. If $m$ and $p^a m$ are two such products, then so is $p^k m$ for all $0 < k < a$. - Yan Sheng Ang, Feb 13 2020
- notes: OEIS A60957 -- https://oeis.org/A60957
- track: open
- answer_shape: proof
- source_stem: 60957
- source_namespace: OeisA60957
- source_theorem: conjecture
- source_category: research open
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4 a_5
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- Number of different products of any subset of $\{1, 2, \dots, n\}$. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.image (·.prod id)).card

/-- The set of products of subsets of $\{1, \dots, n\}$. -/
def productsOfSubsets (n : ℕ) : Set ℕ :=
  {m : ℕ | ∃ s ⊆ Finset.Icc 1 n, m = s.prod id}

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 5 11]
theorem a_0 : a 0 = 1 := by
  decide

@[category test, AMS 5 11]
theorem a_1 : a 1 = 1 := by
  decide

@[category test, AMS 5 11]
theorem a_2 : a 2 = 2 := by
  decide

@[category test, AMS 5 11]
theorem a_3 : a 3 = 4 := by
  decide

@[category test, AMS 5 11]
theorem a_4 : a 4 = 8 := by
  decide

@[category test, AMS 5 11]
theorem a_5 : a 5 = 16 := by
  decide

abbrev Target : Prop :=
    ∀ (n : ℕ) (p : ℕ) (hp : p.Prime) (hpn : p ≤ n)
        (m a_exp : ℕ) (h1 : m ∈ productsOfSubsets n) (h2 : p ^ a_exp * m ∈ productsOfSubsets n)
        (k : ℕ) (hk1 : 0 < k) (hk2 : k < a_exp),
      p ^ k * m ∈ productsOfSubsets n

end Problem
