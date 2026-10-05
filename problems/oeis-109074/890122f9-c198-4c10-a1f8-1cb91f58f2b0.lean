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

- problem_id: O109074_conjecture
- collection: oeis
- question_id: oeis:109074
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/109074.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: "It is conjectured that $\binom{6n-2}{2n} / \left(2 \binom{4n-1}{2n}\right) = \text{A005156}(n+1)/\text{A005156}(n)$." The OEIS comment indexes A005156 from $1$; for the $0$-indexed sequence `b` this states `frac (n + 1) = b (n + 1) / b n`. This holds by the product formula $$\text{A005156}(n) = \frac{1}{2^n} \prod_{k=1}^{n} \frac{(6k-2)!\,(2k-1)!}{(4k-1)!\,(4k-2)!}$$ conjectured by Robbins and proved by Kuperberg (2002).
- notes: OEIS A109074 -- https://oeis.org/A109074
- track: solved
- answer_shape: proof
- source_stem: 109074
- source_namespace: OeisA109074
- source_theorem: conjecture
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: b_0 b_1 b_2 b_3
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Nat

/--
The rational number defined by $\binom{6n-2}{2n} / \left(2 \binom{4n-1}{2n}\right)$,
whose numerator is A109074.
-/
def frac (n : ℕ) : ℚ :=
  let numTerm : ℕ := (6 * n - 2).choose (2 * n)
  let denTerm : ℕ := 2 * ((4 * n - 1).choose (2 * n))
  (numTerm : ℚ) / (denTerm : ℚ)

/--
The primary defining sequence `a`.
$a(n)$ is the numerator of $\binom{6n-2}{2n} / \left(2 \binom{4n-1}{2n}\right)$.
-/
def a (n : ℕ) : ℕ :=
  (frac n).num.natAbs

/--
Lists of length `k` with entries in `{-1, 0, 1}`.
-/
def trinaryLists : ℕ → List (List ℤ)
  | 0 => [[]]
  | k + 1 =>
    (trinaryLists k).flatMap fun xs => [(-1 : ℤ) :: xs, 0 :: xs, 1 :: xs]

/--
Checks that all prefix sums of `xs` starting from `acc` lie in `{0, 1}` and the final sum is `1`.
-/
def isAsmLineAux : ℤ → List ℤ → Bool
  | acc, [] => acc == 1
  | acc, x :: xs =>
    let s := acc + x
    (s == 0 || s == 1) && isAsmLineAux s xs

/--
A list of integers in `{-1, 0, 1}` is a valid alternating sign matrix row/column if all of its
prefix sums lie in `{0, 1}` and its total sum is `1`.
-/
def isAsmLine (xs : List ℤ) : Bool :=
  isAsmLineAux 0 xs

/--
All vertically symmetric alternating sign matrix rows of length `2 * n + 1`.
-/
def symAsmRows (n : ℕ) : List (List ℤ) :=
  (trinaryLists n).flatMap fun half =>
    [(-1 : ℤ), 0, 1].filterMap fun mid =>
      let row := half ++ [mid] ++ half.reverse
      if isAsmLine row then some row else none

/--
Number of ways to complete `k` remaining vertically symmetric ASM rows given the current column
partial sums `colSums`.
-/
def countVsasmRows (rows : List (List ℤ)) : ℕ → List ℤ → ℕ
  | 0, colSums => if colSums.all (· == 1) then 1 else 0
  | k + 1, colSums =>
    let step := countVsasmRows rows k
    rows.foldl (fun acc r =>
      let nextSums := List.zipWith (· + ·) colSums r
      if nextSums.all (fun s => s == 0 || s == 1) then
        acc + step nextSums
      else acc) 0

/--
A005156 (offset 0): the number of $(2n+1) \times (2n+1)$ alternating sign matrices symmetric
about the vertical axis (VSASMs).
-/
def b (n : ℕ) : ℕ :=
  countVsasmRows (symAsmRows n) (2 * n + 1) (List.replicate (2 * n + 1) 0)

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 5 11]
theorem b_0 : b 0 = 1 := by decide

@[category test, AMS 5 11]
theorem b_1 : b 1 = 1 := by decide

@[category test, AMS 5 11]
theorem b_2 : b 2 = 3 := by decide

@[category test, AMS 5 11]
theorem b_3 : b 3 = 26 := by decide

abbrev Target : Prop :=
    ∀ (n : ℕ),
      frac (n + 1) = (b (n + 1) : ℚ) / (b n : ℚ)

end Problem
