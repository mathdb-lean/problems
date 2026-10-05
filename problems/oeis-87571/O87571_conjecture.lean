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

- problem_id: O87571_conjecture
- collection: oeis
- question_id: oeis:87571
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/87571.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture: There are infinitely many composite numbers $n$ such that $a(n)$ is nonzero.
- notes: OEIS A87571 -- https://oeis.org/A87571
- track: open
- answer_shape: proof
- source_stem: 87571
- source_namespace: OeisA87571
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- Concatenate a list of numbers into a list of decimal digits in most-significant-first order. -/
def getAllDigitsMsf (L : List ℕ) : List ℕ :=
  List.flatten (L.map fun k => (Nat.digits 10 k).reverse)

/-- Convert a list of decimal digits (most significant first) to a natural number. -/
def ofDigitsMsf (D : List ℕ) : ℕ :=
  D.foldl (fun acc d => acc * 10 + d) 0

/-- Concatenation of numbers $n, n-1, \dots, n-k$. -/
def concatNum (n : ℕ) (k : ℕ) : ℕ :=
  ofDigitsMsf (getAllDigitsMsf ((List.range (k + 1)).map fun i => n - i))

/-- Smallest prime of the form $n, n-1, \dots, n-k$ for $k < n$, or $0$ if none exists. -/
def a (n : ℕ) : ℕ :=
  match ((List.range n).map (concatNum n)).find? Nat.Prime with
  | some p => p
  | none => 0

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by decide

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 43 := by decide

abbrev Target : Prop :=
    ∀ (M : ℕ),
      ∃ n > M, 1 < n ∧ ¬ n.Prime ∧ a n ≠ 0

end Problem
