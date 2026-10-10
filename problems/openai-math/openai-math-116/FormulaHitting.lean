import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs
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

- problem_id: FormulaHitting
- collection: openai-math
- question_id: openai-math:116
- source: openai-math
- source_locator: lean/ComparatorChallenges/FormulaHitting.lean#OAI.NCHitting.universal_hitting
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: For each characteristic, constructs in deterministic polynomial bit time a polynomial-dimensional matrix tuple detecting every nonzero division-free noncommutative formula of bounded size over any field of that characteristic. Rational formulas over ℚ also admit polynomial-size hitting lists whenever they have a defined rational-matrix evaluation. ([Lean](lean/docs/116.md)) We construct, in deterministic polynomial bit time, one tuple of rational matrices that detects every nonzero polynomial computed by a noncommutative division-free formula of a prescribed size. The matrices have dimension $`O(ns^2)`$ for n variables and formula size s, and the same tuple works over every field of characteristic zero. We construct, in deterministic polynomial bit time, a polynomial-size list of rational matrix tuples for noncommutative rational formulas over ℚ of bounded tree size. Every nonzero admissible formula has a defined, invertible value at one tuple, with no separate bounds on inverse nesting or rational constant heights. Matrix dimensions, entry bit lengths, and total output length are polynomially bounded.
- notes: OpenAI math result family 116, Uniform black-box noncommutative identity testing across characteristics -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/116.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.NCHitting.universal_hitting
- source_theorem_count: 1
- source_solution_module: OAI.Algebra.FormulaHitting.Hitting
- source_papers: preprints/One-Rational-Matrix-Hitting-Point-for-Noncommutative-Formulas-September-24-2026/One-Rational-Matrix-Hitting-Point-for-Noncommutative-Formulas-September-24-2026.pdf preprints/Polynomial-Hitting-Lists-for-Noncommutative-Rational-Formulas-September-24-2026/Polynomial-Hitting-Lists-for-Noncommutative-Rational-Formulas-September-24-2026.pdf
- source_scope_note: lean/docs/116.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace NCHitting

abbrev Word (n : ℕ) := List (Fin n)
abbrev WordSeries (F : Type*) (n : ℕ) := Word n → F

def convolution {F : Type*} {n : ℕ} [Semiring F]
    (f g : WordSeries F n) : Word n → F
  | [] => f [] * g []
  | i :: w => f [] * g (i :: w) + convolution (fun v => f (i :: v)) g w

inductive Formula (F : Type*) (n : ℕ) where
  | scalar : F → Formula F n
  | var : Fin n → Formula F n
  | add : Formula F n → Formula F n → Formula F n
  | mul : Formula F n → Formula F n → Formula F n

namespace Formula

def size {F : Type*} {n : ℕ} : Formula F n → ℕ
  | scalar _ => 1
  | var _ => 1
  | add f g => f.size + g.size + 1
  | mul f g => f.size + g.size + 1

noncomputable def coeff {F : Type*} {n : ℕ} [Semiring F] :
    Formula F n → WordSeries F n
  | scalar a => fun w => if w = [] then a else 0
  | var i => fun w => if w = [i] then 1 else 0
  | add f g => fun w => coeff f w + coeff g w
  | mul f g => convolution (coeff f) (coeff g)

def eval {F A : Type*} {n : ℕ} [Semiring A]
    (scalarMap : F → A) (T : Fin n → A) : Formula F n → A
  | scalar a => scalarMap a
  | var i => T i
  | add f g => eval scalarMap T f + eval scalarMap T g
  | mul f g => eval scalarMap T f * eval scalarMap T g

end Formula

def dimension (n s : ℕ) : ℕ := if n = 1 ∧ s = 1 then 1 else 2 * n * s ^ 2

def matrixEntry (i r q : ℕ) : ℚ :=
  if q < r then (-1 : ℚ) ^ (r - q - 1) / ((r : ℚ) * (i : ℚ) ^ (r - q))
  else 0

def generator (n s : ℕ) : Fin n → Matrix (Fin (dimension n s)) (Fin (dimension n s)) ℚ :=
  fun i r q => if n = 1 ∧ s = 1 then 1 else matrixEntry (i.val + 1) r.val q.val

universe u_2

def universal_hitting_statement : Prop :=
  ∀ (n s : ℕ) (hn : 1 ≤ n) (hs : 1 ≤ s) (F : Type u_2) [Field F] [CharZero F] (f : Formula F n) (hsize : f.size ≤ s) (hf : ∃ w, f.coeff w ≠ 0),
    f.eval (Matrix.scalar (Fin (dimension n s)))
      (fun i r q => (generator n s i r q : F)) ≠ 0

end NCHitting

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u_2} : Prop :=
  _root_.OAI.NCHitting.universal_hitting_statement.{u_2}

end Problem

/- Formalization scope, from lean/docs/116.md: The formalization gives one explicit tuple of rational matrices that simultaneously detects every nonzero division-free noncommutative formula with at most $s$ gates in $n$ variables, for $n,s\ge1$. Evaluation at that tuple is a nonzero matrix over every characteristic-zero field. The selected theorem states this universal hitting property. The paper's deterministic polynomial bit-construction bound and matrix-dimension bound $O(ns^2)$ are not separately asserted in it. The formalized result constructs polynomial-size hitting lists for noncommutative rational formulas with rational constants, addition, multiplication, and inverse gates. Given the number of variables and a formula-size bound, one deterministic polynomial-time machine outputs rational matrix tuples of a common positive dimension. Every admissible nonzero formula within the size bound evaluates to an invertible matrix on some listed tuple. The matrix dimension, complete binary output length, and running time are all polynomially bounded. -/
