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

- problem_id: O182126_conjecture1
- collection: oeis
- question_id: oeis:182126
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/182126.lean#conjecture1
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture: For $x > 10^9$, the most frequent value in $a(n)$, $n=1\dots x$, has form $120k$.
- notes: OEIS A182126 -- https://oeis.org/A182126
- track: open
- answer_shape: proof
- source_stem: 182126
- source_namespace: OeisA182126
- source_theorem: conjecture1
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_1 a_2 a_3 a_4
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- $\mathrm{prime}(k)$ is the $k$-th prime number ($\mathrm{prime}(1) = 2$). -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- $a(n) = \mathrm{prime}(n) \cdot \mathrm{prime}(n+1) \bmod \mathrm{prime}(n+2)$. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else (prime n * prime (n + 1)) % prime (n + 2)

/-- Count of occurrences of value $v$ among $a(1), \dots, a(x)$. -/
noncomputable def countA (x v : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun n => 1 ≤ n ∧ a n = v).card

/-- $v_0$ is a most frequent value among $a(1), \dots, a(x)$. -/
def IsMostFrequent (x v₀ : ℕ) : Prop :=
  ∀ v : ℕ, countA x v ≤ countA x v₀

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  have h0 : Nat.nth Nat.Prime 0 = 2 := (2).nth_count (by decide : (2).Prime)
  have h1 : Nat.nth Nat.Prime 1 = 3 := (3).nth_count (by decide : (3).Prime)
  have h2 : Nat.nth Nat.Prime 2 = 5 := (5).nth_count (by decide : (5).Prime)
  show (Nat.nth Nat.Prime 0 * Nat.nth Nat.Prime 1) % Nat.nth Nat.Prime 2 = 1
  rw [h0, h1, h2]

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  have h1 : Nat.nth Nat.Prime 1 = 3 := (3).nth_count (by decide : (3).Prime)
  have h2 : Nat.nth Nat.Prime 2 = 5 := (5).nth_count (by decide : (5).Prime)
  have h3 : Nat.nth Nat.Prime 3 = 7 := (7).nth_count (by decide : (7).Prime)
  show (Nat.nth Nat.Prime 1 * Nat.nth Nat.Prime 2) % Nat.nth Nat.Prime 3 = 1
  rw [h1, h2, h3]

@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by
  have h2 : Nat.nth Nat.Prime 2 = 5 := (5).nth_count (by decide : (5).Prime)
  have h3 : Nat.nth Nat.Prime 3 = 7 := (7).nth_count (by decide : (7).Prime)
  have h4 : Nat.nth Nat.Prime 4 = 11 := (11).nth_count (by decide : (11).Prime)
  show (Nat.nth Nat.Prime 2 * Nat.nth Nat.Prime 3) % Nat.nth Nat.Prime 4 = 2
  rw [h2, h3, h4]

@[category test, AMS 11]
theorem a_4 : a 4 = 12 := by
  have h3 : Nat.nth Nat.Prime 3 = 7 := (7).nth_count (by decide : (7).Prime)
  have h4 : Nat.nth Nat.Prime 4 = 11 := (11).nth_count (by decide : (11).Prime)
  have h5 : Nat.nth Nat.Prime 5 = 13 := (13).nth_count (by decide : (13).Prime)
  show (Nat.nth Nat.Prime 3 * Nat.nth Nat.Prime 4) % Nat.nth Nat.Prime 5 = 12
  rw [h3, h4, h5]

abbrev Target : Prop :=
    ∀ (x : ℕ) (hx : 10 ^ 9 < x) (v₀ : ℕ) (hv : IsMostFrequent x v₀),
      120 ∣ v₀

end Problem
