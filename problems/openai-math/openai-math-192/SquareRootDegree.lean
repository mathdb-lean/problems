import Mathlib
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

- problem_id: SquareRootDegree
- collection: openai-math
- question_id: openai-math:192
- source: openai-math
- source_locator: lean/ComparatorChallenges/SquareRootDegree.lean#OAI.SquareRootDegree.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Disproves the proposed square-root bound relating a Boolean function's linear Fourier coefficients to its polynomial degree. For every C &gt; 0, there is a sign-valued Boolean function f with $`\sum_i\widehat f(\{i\})\gt C\sqrt{\deg(f)}`$. Thus its total signed correlation with individual input bits can exceed the proposed bound by an arbitrary factor. ([Lean](lean/docs/192.md)) We disprove the Gopalan–Servedio square-root conjecture, even up to an arbitrary constant factor. For every real C &gt; 0, there is a nonconstant Boolean function $`f:\{-1,1\}^n\to\{-1,1\}`$ on a finite sign cube such that
- notes: OpenAI math result family 192, Boolean functions violate the square-root degree bound by arbitrary factors -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/192.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.SquareRootDegree.main
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.BooleanFunctions.Main
- source_papers: preprints/Unbounded-Violations-of-the-Square-Root-Degree-Bound-September-26-2026/Unbounded-Violations-of-the-Square-Root-Degree-Bound-September-26-2026.pdf
- source_scope_note: lean/docs/192.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-!
Bool encodes a sign: false is +1 and true is -1. The average is uniform,
and degree is ordinary real Fourier degree, not F₂ degree or threshold degree.
-/

open scoped BigOperators

noncomputable section

namespace SquareRootDegree

abbrev Cube (ι : Type*) := ι → Bool

def sign (b : Bool) : ℝ := if b then -1 else 1

def average {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ)⁻¹ * ∑ x, f x

def character {ι : Type*} (s : Finset ι) (x : Cube ι) : ℝ :=
  ∏ i ∈ s, sign (x i)

def fourierCoeff {ι : Type*} [Fintype ι] (f : Cube ι → ℝ) (s : Finset ι) : ℝ := by
  classical
  exact average (fun x => f x * character s x)

def fourierDegree {ι : Type*} [Fintype ι] (f : Cube ι → ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun s : Finset ι => fourierCoeff f s ≠ 0)).sup Finset.card

def IsBoolean {α : Type*} (f : α → ℝ) : Prop :=
  ∀ x, f x = -1 ∨ f x = 1

def Nonconstant {α : Type*} (f : α → ℝ) : Prop :=
  ∃ x y, f x ≠ f y

def singletonSum {ι : Type*} [Fintype ι] (f : Cube ι → ℝ) : ℝ :=
  ∑ i, fourierCoeff f {i}

def absoluteSingletonSum {ι : Type*} [Fintype ι] (f : Cube ι → ℝ) : ℝ :=
  ∑ i, |fourierCoeff f {i}|

def SignedViolations : Prop :=
  ∀ C : ℝ, 0 < C → ∃ n : ℕ, 0 < n ∧ ∃ f : Cube (Fin n) → ℝ,
    IsBoolean f ∧ Nonconstant f ∧ C * Real.sqrt (fourierDegree f) < singletonSum f

def AbsoluteRatios : Set ℝ :=
  {r | ∃ n : ℕ, 0 < n ∧ ∃ f : Cube (Fin n) → ℝ,
    IsBoolean f ∧ 0 < fourierDegree f ∧
      r = absoluteSingletonSum f / Real.sqrt (fourierDegree f)}

/-- The two clauses of the literal main theorem. Unboundedness above is the
real-valued formulation of the displayed supremum being positive infinity. -/
def main_statement : Prop :=
  SignedViolations ∧ ¬ BddAbove AbsoluteRatios

end SquareRootDegree

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.SquareRootDegree.main_statement

end Problem

/- Formalization scope, from lean/docs/192.md: The formalization disproves the Gopalan–Servedio square-root degree conjecture by an unbounded factor. For every $C>0$, it gives a nonconstant Boolean function on a finite sign cube for which the sum of its linear Fourier coefficients exceeds $C\sqrt{\deg f}$, where $\deg f$ is its real multilinear degree. It also proves that the ratio of the sum of the absolute values of those coefficients to $\sqrt{\deg f}$ is unbounded among positive-degree Boolean functions. -/
