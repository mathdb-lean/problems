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

- problem_id: O141057_conjecture2
- collection: oeis
- question_id: oeis:141057
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/141057.lean#conjecture2
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture (Peter Bala, 2022): The supercongruences $a(n \cdot p^k) \equiv a(n \cdot p^{k-1}) \pmod{p^{3k}}$ hold for the integer-indexed extension $a(n)$ for all $n \in \mathbb{Z} \setminus \{0\}$, primes $p \ge 5$, and $k \ge 1$.
- notes: OEIS A141057 -- https://oeis.org/A141057
- track: open
- answer_shape: proof
- source_stem: 141057
- source_namespace: OeisA141057
- source_theorem: conjecture2
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4 aInt_neg_1 aInt_neg_2
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- Number of Abelian cubes of length $3n$ over an alphabet of size 3. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k ^ 3) * ∑ j ∈ Finset.range (k + 1), (k.choose j ^ 3)

/-- Extension of the sequence $a$ to all integers $n \in \mathbb{Z}$.
For $n < 0$, $a(n) = \sum_{k=0}^{-n} \binom{n}{k}^3 \sum_{j=0}^k \binom{k}{j}^3$,
where $\binom{n}{k} = (-1)^k \binom{-n+k-1}{k}$. -/
def aInt (n : ℤ) : ℤ :=
  if 0 ≤ n then
    let nNat := n.toNat
    (∑ k ∈ Finset.range (nNat + 1), (nNat.choose k ^ 3) * ∑ j ∈ Finset.range (k + 1), (k.choose j ^ 3) : ℕ)
  else
    let nNat := (-n).toNat
    ∑ k ∈ Finset.range (nNat + 1), ((-1 : ℤ) ^ k * (nNat + k - 1).choose k : ℤ) ^ 3 *
      ∑ j ∈ Finset.range (k + 1), ((k.choose j : ℤ) ^ 3)

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 3 := by decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 27 := by decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 381 := by decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 6219 := by decide

/-- Value of the sequence `aInt` at -1. -/
@[category test, AMS 11]
theorem aInt_neg_1 : aInt (-1) = -1 := by decide

/-- Value of the sequence `aInt` at -2. -/
@[category test, AMS 11]
theorem aInt_neg_2 : aInt (-2) = 255 := by decide

abbrev Target : Prop :=
    ∀ (p k : ℕ) (n : ℤ) (hp : p.Prime) (h_p_ge_5 : 5 ≤ p) (h_k_pos : 1 ≤ k)
        (hn : n ≠ 0),
      aInt (n * (p ^ k : ℤ)) ≡ aInt (n * (p ^ (k - 1) : ℤ)) [ZMOD (p ^ (3 * k) : ℤ)]

end Problem
