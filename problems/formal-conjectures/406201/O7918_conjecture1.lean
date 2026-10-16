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

- problem_id: O7918_conjecture1
- collection: oeis
- question_id: oeis:7918
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/7918.lean#conjecture1
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: According to the "k-tuple" conjecture, $a(n)$ is the initial term of the lexicographically earliest increasing arithmetic progression of $n$ primes; the corresponding common differences are given by A061558.
- notes: OEIS A7918 -- https://oeis.org/A7918
- track: open
- answer_shape: proof
- source_stem: 7918
- source_namespace: OeisA7918
- source_theorem: conjecture1
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- Least prime $\ge n$ (version 1 of the "next prime" function). -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { p : ℕ | p.Prime ∧ n ≤ p }

/--
The initial term $p_0$ and common difference $d$ form an arithmetic progression of
length $n$ consisting entirely of prime numbers with $d > 0$.
-/
def isApOfNPrimes (n p0 d : ℕ) : Prop :=
  d > 0 ∧ ∀ k < n, (p0 + k * d).Prime

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 2 := by
  dsimp [a]
  have h : IsLeast { p : ℕ | p.Prime ∧ 0 ≤ p } 2 :=
    ⟨⟨Nat.prime_two, Nat.zero_le 2⟩, fun p hp ↦ hp.1.two_le⟩
  exact h.csInf_eq

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  dsimp [a]
  have h : IsLeast { p : ℕ | p.Prime ∧ 1 ≤ p } 2 :=
    ⟨⟨Nat.prime_two, by decide⟩, fun p hp ↦ hp.1.two_le⟩
  exact h.csInf_eq

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by
  dsimp [a]
  have h : IsLeast { p : ℕ | p.Prime ∧ 2 ≤ p } 2 :=
    ⟨⟨Nat.prime_two, le_rfl⟩, fun p hp ↦ hp.1.two_le⟩
  exact h.csInf_eq

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by
  dsimp [a]
  have h : IsLeast { p : ℕ | p.Prime ∧ 3 ≤ p } 3 :=
    ⟨⟨Nat.prime_three, le_rfl⟩, fun p hp ↦ hp.2⟩
  exact h.csInf_eq

abbrev Target : Prop :=
    ∀ (n : ℕ) (hn : 0 < n),
      a n = sInf { p0 : ℕ | ∃ d : ℕ, isApOfNPrimes n p0 d }

end Problem
