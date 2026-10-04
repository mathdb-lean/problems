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

- problem_id: E482
- collection: erdos
- question_id: erdos:482
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/482.lean#erdos_482
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Define a sequence by $a_1=1$ and $$a_{n+1}=\lfloor\sqrt{2}(a_n+1/2)\rfloor$$ for $n\geq 1$. The difference $a_{2n+1}-2a_{2n-1}$ is the $n$th digit in the binary expansion of $\sqrt{2}$. Find similar results for $\theta=\sqrt{m}$, and other algebraic numbers. The result for $\sqrt{2}$ was obtained by Graham and Pollak [GrPo70]. The problem statement is open-ended, but presumably Erdős and Graham would have been satisfied with the wide-ranging generalisations of Stoll ([St05] and [St06]). The binary expansion is $\sqrt{2} = 1.0110101\ldots$, and the $n$th digit counts the leading $1$ as digit $1$. It is stated with Mathlib's `Real.digits`: the $n$th digit of $\sqrt{2}$ is digit $n - 1$ of $\sqrt{2}/2 = 0.10110101\ldots$, that is $\lfloor \sqrt{2} \cdot 2^{n-1} \rfloor \bmod 2$. The second conjunct records that these digits are the binary expansion: they reconstruct $\sqrt{2}/2$.
- notes: Erdos Problem 482 -- https://www.erdosproblems.com/482
- track: solved
- answer_shape: proof
- source_stem: 482
- mathdb_ref: erdos:482
- source_namespace: Erdos482
- source_theorem: erdos_482
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- The sequence of the problem: $a_1 = 1$ and $a_{n+1} = \lfloor \sqrt{2}(a_n + 1/2) \rfloor$ for
$n \geq 1$. The value $a_0$ is not used. -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => ⌊√2 * ((a (n + 1) : ℝ) + 1 / 2)⌋₊

/-- Stoll's general Graham–Pollak-type recurrence in base $g$, with real parameters $a$, $b$, and
$\varepsilon$. Its even-index differences are used to read base-$g$ digits. -/
noncomputable def generalRecurrence (g : ℕ) (a b ε : ℝ) : ℕ → ℤ
  | 0 => 1
  | n + 1 =>
      if Even n then ⌊a * ((generalRecurrence g a b ε n : ℝ) + ε)⌋
      else ⌊b * ((generalRecurrence g a b ε n : ℝ) + 1 / ((g : ℝ) - 1))⌋

/-- The odd-step coefficient of the Rabinowitz–Gilbert/Stoll binary recurrence. -/
noncomputable def alpha (t : ℝ) : ℝ := 2 * (t + 1) / (t + 2)

/-- The even-step coefficient of the Rabinowitz–Gilbert/Stoll binary recurrence. -/
noncomputable def beta (t : ℝ) : ℝ := (t + 2) / (t + 1)

/-- Zero-based form of the Rabinowitz–Gilbert/Stoll binary recurrence: `stollBinary t k` is the
paper's $u_{k+1}$.  At $t = \sqrt{2}$ both coefficients equal $\sqrt{2}$, and this is the sequence
`a` shifted by one. -/
noncomputable def stollBinary (t : ℝ) : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      ⌊(if Even n then alpha t else beta t) * ((stollBinary t n : ℝ) + 1 / 2)⌋₊

/-- The binary digits of a normalized real $t \in [1, 2)$, indexed from one and including the
leading digit.  The value at index zero is padding. -/
noncomputable def binaryDigit (t : ℝ) : ℕ → Fin 2
  | 0 => 0
  | 1 => 1
  | k + 2 => Real.digits (t - 1) 2 k

abbrev Target : Prop :=
    (∀ n : ℕ, 1 ≤ n →
      (a (2 * n + 1) : ℤ) - 2 * a (2 * n - 1) = (Real.digits (√2 / 2) 2 (n - 1) : ℕ)) ∧
      Real.ofDigits (Real.digits (√2 / 2) 2) = √2 / 2

end Problem
