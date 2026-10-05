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

- problem_id: O303639_conjecture
- collection: oeis
- question_id: oeis:303639
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/303639.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Zhi-Wei Sun's Conjecture (A303639)**: any integer $n > 1$ can be written as $a^2 + b^2 + \binom{2c+1}{c} + \binom{2d+1}{d}$ with $a, b, c, d$ nonnegative integers. Sun checked this for $n$ up to $6 \cdot 10^8$. This is false: $n = 800322180$ admits no such representation, so $a(800322180) = 0$. Since $\binom{33}{16} > 800322180$, only $c, d \le 15$ are possible, and each of the resulting $136$ remainders $800322180 - \binom{2c+1}{c} - \binom{2d+1}{d}$ is divisible by some prime $p \equiv 3 \pmod 4$ to an odd power, hence is not a sum of two squares by Fermat's two-square theorem. The counterexample is recorded as an approved comment on the OEIS entry; the Lean proof linked below formalises this argument, and was produced by Claude Opus 5 prompted by Sunsu Jeong ([DCLXAI](https://github.com/DCLXAI)).
- notes: OEIS A303639 -- https://oeis.org/A303639
- track: solved
- answer_shape: proof
- source_stem: 303639
- source_namespace: OeisA303639
- source_theorem: conjecture
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_1 a_2 a_3 a_4 a_5 a_6
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- The predicate that $n$ can be written as $a^2 + b^2 + \binom{2c+1}{c} + \binom{2d+1}{d}$
for nonnegative integers $a, b, c, d$.

This drops the normalisations $a \le b$ and $c \le d$. They do not affect whether the count is
positive, and refuting the unordered statement is the stronger result, since a representation
with $a \le b$ and $c \le d$ is in particular a representation. -/
def A (n : ℕ) : Prop :=
  ∃ a b c d : ℕ, n = a ^ 2 + b ^ 2 + (2 * c + 1).choose c + (2 * d + 1).choose d

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_1 : ¬ A 1 := by
  rintro ⟨a, b, c, d, h⟩
  have hc : 0 < (2 * c + 1).choose c := Nat.choose_pos (by omega)
  have hd : 0 < (2 * d + 1).choose d := Nat.choose_pos (by omega)
  omega

@[category test, AMS 11]
theorem a_2 : A 2 :=
  ⟨0, 0, 0, 0, by decide⟩

@[category test, AMS 11]
theorem a_3 : A 3 :=
  ⟨1, 0, 0, 0, by decide⟩

@[category test, AMS 11]
theorem a_4 : A 4 :=
  ⟨0, 0, 0, 1, by decide⟩

@[category test, AMS 11]
theorem a_5 : A 5 :=
  ⟨1, 0, 0, 1, by decide⟩

@[category test, AMS 11]
theorem a_6 : A 6 :=
  ⟨2, 0, 0, 0, by decide⟩

abbrev Target : Prop :=
    ¬ ∀ n : ℕ, 1 < n → A n

end Problem
