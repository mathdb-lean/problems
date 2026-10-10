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

- problem_id: RationalHitting
- collection: openai-math
- question_id: openai-math:116
- source: openai-math
- source_locator: lean/ComparatorChallenges/RationalHitting.lean#OAI.RationalHitting.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: For each characteristic, constructs in deterministic polynomial bit time a polynomial-dimensional matrix tuple detecting every nonzero division-free noncommutative formula of bounded size over any field of that characteristic. Rational formulas over ℚ also admit polynomial-size hitting lists whenever they have a defined rational-matrix evaluation. ([Lean](lean/docs/116.md)) We construct, in deterministic polynomial bit time, one tuple of rational matrices that detects every nonzero polynomial computed by a noncommutative division-free formula of a prescribed size. The matrices have dimension $`O(ns^2)`$ for n variables and formula size s, and the same tuple works over every field of characteristic zero. We construct, in deterministic polynomial bit time, a polynomial-size list of rational matrix tuples for noncommutative rational formulas over ℚ of bounded tree size. Every nonzero admissible formula has a defined, invertible value at one tuple, with no separate bounds on inverse nesting or rational constant heights. Matrix dimensions, entry bit lengths, and total output length are polynomially bounded.
- notes: OpenAI math result family 116, Uniform black-box noncommutative identity testing across characteristics -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/116.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.RationalHitting.main
- source_theorem_count: 1
- source_solution_module: OAI.Computability.RationalHitting.Main
- source_main_result: OAI.RationalHitting.main
- source_papers: preprints/One-Rational-Matrix-Hitting-Point-for-Noncommutative-Formulas-September-24-2026/One-Rational-Matrix-Hitting-Point-for-Noncommutative-Formulas-September-24-2026.pdf preprints/Polynomial-Hitting-Lists-for-Noncommutative-Rational-Formulas-September-24-2026/Polynomial-Hitting-Lists-for-Noncommutative-Rational-Formulas-September-24-2026.pdf
- source_scope_note: lean/docs/116.md
- source_field: Computability
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace RationalHitting

universe u

inductive Formula (n : ℕ) where
  | var : Fin n → Formula n
  | const : ℚ → Formula n
  | add : Formula n → Formula n → Formula n
  | mul : Formula n → Formula n → Formula n
  | inv : Formula n → Formula n
  deriving DecidableEq

namespace Formula

def size {n : ℕ} : Formula n → ℕ
  | .var _ | .const _ => 1
  | .add f g | .mul f g => f.size + g.size + 1
  | .inv f => f.size + 1

/-- Evaluation in any rational algebra; a unary inverse requires an actual
    two-sided inverse of the evaluated operand, not a totalized inverse. -/
inductive Eval {n : ℕ} {R : Type u} [Ring R]
    (c : ℚ →+* R) (X : Fin n → R) : Formula n → R → Prop where
  | var (i) : Eval c X (.var i) (X i)
  | const (a) : Eval c X (.const a) (c a)
  | add {f g a b} : Eval c X f a → Eval c X g b → Eval c X (.add f g) (a + b)
  | mul {f g a b} : Eval c X f a → Eval c X g b → Eval c X (.mul f g) (a * b)
  | inv {f a b} : Eval c X f a → a * b = 1 → b * a = 1 → Eval c X (.inv f) b

end Formula

abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℚ
abbrev Tuple (n d : ℕ) := Fin n → Mat d

def Evaluates {n d : ℕ} (f : Formula n) (X : Tuple n d) (v : Mat d) : Prop :=
  f.Eval (algebraMap ℚ (Mat d)) X v

def Admissible {n : ℕ} (f : Formula n) : Prop :=
  ∃ d, 0 < d ∧ ∃ (X : Tuple n d), ∃ v, Evaluates f X v

def Nonzero {n : ℕ} (f : Formula n) : Prop :=
  ∃ d, 0 < d ∧ ∃ (X : Tuple n d), ∃ v, Evaluates f X v ∧ v ≠ 0

/-- All output tuples have one common positive dimension. -/
structure Output (n : ℕ) where
  dimension : ℕ
  dimension_pos : 0 < dimension
  tuples : List (Tuple n dimension)

/-- Little-endian unsigned binary, prefixed by a unary bit-length and a zero
    terminator. This is a self-delimiting binary encoding, including zero. -/
def encodeNat (a : ℕ) : List Bool :=
  let ds := (Nat.digits 2 a).map (fun b => b != 0)
  List.replicate ds.length true ++ [false] ++ ds

/-- Sign bit, binary numerator magnitude, and positive binary denominator.
    Rat.num and Rat.den are the canonical reduced numerator and denominator. -/
def encodeRat (a : ℚ) : List Bool :=
  [decide (a.num < 0)] ++ encodeNat a.num.natAbs ++ encodeNat a.den

def encodeTuple {n d : ℕ} (X : Tuple n d) : List Bool :=
  (List.finRange n).flatMap fun i =>
    (List.finRange d).flatMap fun j =>
      (List.finRange d).flatMap fun k => encodeRat (X i j k)

def encodeOutput {n : ℕ} (H : Output n) : List Bool :=
  encodeNat H.dimension ++ encodeNat H.tuples.length ++ H.tuples.flatMap encodeTuple

/-- 0 is blank, 1 and 2 are the two literal binary digits, 3 is work space.
    Fixed finite tape alphabet and finite state space; no advice or oracle. -/
abbrev Alphabet := Fin 4
abbrev Machine (m : ℕ) := Turing.TM0.Machine Alphabet (Fin (m + 1))
abbrev Config (m : ℕ) := Turing.TM0.Cfg Alphabet (Fin (m + 1))

def tapeBit (b : Bool) : Alphabet := if b then 2 else 1

def unaryInput (n s : ℕ) : List Alphabet :=
  List.replicate n 2 ++ [1] ++ List.replicate s 2

/-- Exactly t ordinary deterministic TM0 transitions. -/
def run {m : ℕ} (G : Machine m) : ℕ → Config m → Option (Config m)
  | 0, a => some a
  | t + 1, a => (Turing.TM0.step G a).bind (run G t)

def OutputsWithin {m n : ℕ} (G : Machine m) (s bound : ℕ) (H : Output n) : Prop :=
  ∃ t ≤ bound, ∃ a : Config m,
    run G t (Turing.TM0.init (unaryInput n s)) = some a ∧
    Turing.TM0.step G a = none ∧
    a.Tape.right₀ = Turing.ListBlank.mk ((encodeOutput H).map tapeBit)

def Hits {n : ℕ} (s : ℕ) (H : Output n) : Prop :=
  ∀ f : Formula n, f.size ≤ s → Admissible f → Nonzero f →
    ∃ X ∈ H.tuples, ∃ v, Evaluates f X v ∧ IsUnit v

/-- A fixed polynomial bound on bit time, full binary output length,
and common positive dimension. -/
def MainStatement : Prop :=
  ∃ (m : ℕ) (G : Machine m) (C k : ℕ), 0 < C ∧ 0 < k ∧
    ∀ n s : ℕ, 1 ≤ n → 1 ≤ s → ∃ H : Output n,
      H.dimension ≤ C * (n + s + 1) ^ k ∧
      (encodeOutput H).length ≤ C * (n + s + 1) ^ k ∧
      OutputsWithin G s (C * (n + s + 1) ^ k) H ∧ Hits s H

def main_statement : Prop :=
  MainStatement

end RationalHitting

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.RationalHitting.main_statement

end Problem

/- Formalization scope, from lean/docs/116.md: The formalization gives one explicit tuple of rational matrices that simultaneously detects every nonzero division-free noncommutative formula with at most $s$ gates in $n$ variables, for $n,s\ge1$. Evaluation at that tuple is a nonzero matrix over every characteristic-zero field. The selected theorem states this universal hitting property. The paper's deterministic polynomial bit-construction bound and matrix-dimension bound $O(ns^2)$ are not separately asserted in it. The formalized result constructs polynomial-size hitting lists for noncommutative rational formulas with rational constants, addition, multiplication, and inverse gates. Given the number of variables and a formula-size bound, one deterministic polynomial-time machine outputs rational matrix tuples of a common positive dimension. Every admissible nonzero formula within the size bound evaluates to an invertible matrix on some listed tuple. The matrix dimension, complete binary output length, and running time are all polynomially bounded. -/
