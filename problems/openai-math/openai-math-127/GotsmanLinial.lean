import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
/-
Copyright 2026 OpenAI. Licensed under the Apache License, Version 2.0.
Copyright 2026 The mathdb-lean Authors.

The definitions and the statements below are OpenAI's, from
github.com/openai/math at the revision named in the metadata block; see NOTICE.
What this library changed: each `sorry`-bodied theorem became the definition of
the proposition it stated, and `Problem.Target` conjoins those propositions.

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

/-!
Converted from github.com/openai/math. `source_locator` names the comparator
challenge this came from and `source_solution_module` the module there that
proves it; both are at `source_version`. The definitions are the challenge's
own; each sorried theorem became `<name>_statement`, and `Problem.Target`
below conjoins them. `track` is solved because comparator accepted OpenAI's
proof against this very statement. Whether the statement says what the paper's
title says is what the scope note, carried as a caveat, is about.

- problem_id: GotsmanLinial
- collection: openai-math
- question_id: openai-math:127
- source: openai-math
- source_locator: lean/ComparatorChallenges/GotsmanLinial.lean#OAI.LeanBlast.GotsmanLinial.gotsmanLinialStatement
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that a degree-at-most-d polynomial threshold function on the uniform n-dimensional Boolean cube has average sensitivity at most $`8d\sqrt n`$, uniformly for $`1\le d\le n`$. Average sensitivity counts expected output changes under single-bit flips. This establishes the asymptotic Gotsman–Linial conjecture, allowing polynomial zeros with $`\mathop{\mathrm{sign}}\nolimits (0)=1`$. ([Lean](lean/docs/127.md)) For every n ≥ 1 and $`1\le d\le n`$, we prove that a polynomial threshold function of degree at most d on the uniform Boolean cube has average sensitivity at most $`8d\sqrt n`$. This proves the asymptotic form of the Gotsman–Linial conjecture. The bound is uniform in both parameters and uses the convention $`\mathop{\mathrm{sgn}}\nolimits (0)=1`$.
- notes: OpenAI math result family 127, Average sensitivity of polynomial threshold functions -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/127.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.LeanBlast.GotsmanLinial.gotsmanLinialStatement
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.GotsmanLinial.Main
- source_main_result: OAI.LeanBlast.GotsmanLinial.gotsmanLinialStatement
- source_papers: preprints/Average-Sensitivity-of-Polynomial-Threshold-Functions-September-25-2026/main.pdf
- source_scope_note: lean/docs/127.md
- source_field: Combinatorics
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

abbrev Cube (n : ℕ) := Fin n → Bool

def cubeCoord {n : ℕ} (x : Cube n) (i : Fin n) : ℝ :=
  if x i then 1 else -1

def flip {n : ℕ} (i : Fin n) (x : Cube n) : Cube n :=
  Function.update x i (!(x i))

noncomputable def thresholdSign (t : ℝ) : ℝ :=
  if 0 ≤ t then 1 else -1

noncomputable def sensitiveVertices {n : ℕ} (f : Cube n → ℝ) (i : Fin n) :
    Finset (Cube n) := by
  classical
  exact Finset.univ.filter fun x => f x ≠ f (flip i x)

noncomputable def averageSensitivity {n : ℕ} (f : Cube n → ℝ) : ℝ :=
  ∑ i : Fin n, ((sensitiveVertices f i).card : ℝ) / (2 : ℝ) ^ n

def IsMultilinear {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ m ∈ p.support, ∀ i : Fin n, m i ≤ 1

noncomputable def polynomialValue {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (x : Cube n) : ℝ :=
  MvPolynomial.eval (cubeCoord x) p

noncomputable def polynomialThreshold {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    Cube n → ℝ :=
  fun x => thresholdSign (polynomialValue p x)

def GotsmanLinialStatement : Prop :=
  ∀ (n d : ℕ), 1 ≤ n → 1 ≤ d → d ≤ n →
    ∀ p : MvPolynomial (Fin n) ℝ,
      IsMultilinear p → p.totalDegree ≤ d →
        averageSensitivity (polynomialThreshold p) ≤ 8 * (d : ℝ) * Real.sqrt (n : ℝ)

def gotsmanLinialStatement_statement : Prop :=
  GotsmanLinialStatement

end LeanBlast.GotsmanLinial

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.LeanBlast.GotsmanLinial.gotsmanLinialStatement_statement

end Problem

/- Formalization scope, from lean/docs/127.md: The formalized result proves the average-sensitivity bound $8d\sqrt n$ for every Boolean threshold function defined by a real multilinear polynomial of degree at most $d$ on the $n$-dimensional cube. The sign convention assigns value $1$ at zero. This establishes the stated asymptotic bound, rather than the separate conjecture identifying exact extremizers. -/
