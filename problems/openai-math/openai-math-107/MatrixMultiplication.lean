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

- problem_id: MatrixMultiplication
- collection: openai-math
- question_id: openai-math:107
- source: openai-math
- source_locator: lean/ComparatorChallenges/MatrixMultiplication.lean#OAI.MatrixMultiplication.complex_omega_le_nine_quarters
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves $`\omega\le9/4`$ over ℂ, giving $`O_\varepsilon(n^{9/4+\varepsilon})`$ arithmetic operations for square matrix multiplication. In characteristic zero, some inner dimension na with a &gt; 0.465 permits $`n^{2+o(1)}`$ rectangular multiplication. Further square bounds give ω &lt; 2.258 outside finitely many positive characteristics and ω &lt; 2.371054886006746 over every fixed field. ([Lean](lean/docs/107.md)) — secondary writeup We prove that the arithmetic exponent of square matrix multiplication over every fixed field satisfies ω &lt; 2.371054886006746. This includes every positive characteristic.
- notes: OpenAI math result family 107, Matrix multiplication with exponent at most 9/4 -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/107.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.MatrixMultiplication.complex_omega_le_nine_quarters OAI.MatrixMultiplication.complex_alpha_gt_93_div_200 OAI.MatrixMultiplication.complex_rectangular_omega_lt_523_div_250
- source_theorem_count: 3
- source_solution_module: OAI.LinearAlgebra.MatrixMultiplication.Main
- source_main_result: OAI.MatrixMultiplication.complex_rectangular_omega_lt_523_div_250
- source_papers: preprints/Complex-Matrix-Multiplication-Below-2.258-and-Rectangular-Bounds-September-24-2026/Complex-Matrix-Multiplication-Below-2.258-and-Rectangular-Bounds-September-24-2026.pdf preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf
- source_scope_note: lean/docs/107.md
- source_field: LinearAlgebra
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-! The three main complex matrix multiplication bounds, checked independently. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

inductive Gate (F Input Register : Type*) where
  | constant : F → Gate F Input Register
  | input : Input → Gate F Input Register
  | add : Register → Register → Gate F Input Register
  | sub : Register → Register → Gate F Input Register
  | mul : Register → Register → Gate F Input Register

namespace Gate

variable {F Input Register : Type*}

def eval [Field F] (inputs : Input → F) (registers : Register → F) :
    Gate F Input Register → F
  | .constant z => z
  | .input i => inputs i
  | .add i j => registers i + registers j
  | .sub i j => registers i - registers j
  | .mul i j => registers i * registers j

def cost : Gate F Input Register → ℕ
  | .constant _ => 0
  | .input _ => 0
  | .add _ _ => 1
  | .sub _ _ => 1
  | .mul _ _ => 1

end Gate

inductive Program (F Input : Type*) : ℕ → Type _ where
  | nil : Program F Input 0
  | step {r : ℕ} : Program F Input r → Gate F Input (Fin r) → Program F Input (r + 1)

namespace Program

variable {F Input : Type*}

def eval [Field F] : {r : ℕ} → Program F Input r → (Input → F) → Fin r → F
  | 0, .nil, _ => Fin.elim0
  | _ + 1, .step p g, inputs =>
    Fin.cases (g.eval inputs (p.eval inputs)) (p.eval inputs)

def cost : {r : ℕ} → Program F Input r → ℕ
  | 0, .nil => 0
  | _ + 1, .step p g => p.cost + g.cost

end Program

abbrev MatrixInput (a b c : ℕ) := (Fin a × Fin b) ⊕ (Fin b × Fin c)

def matrixInputs {F : Type*} {a b c : ℕ}
    (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F) :
    MatrixInput a b c → F
  | .inl (i, j) => A i j
  | .inr (j, k) => B j k

structure MatrixAlgorithm (F : Type*) (a b c : ℕ) where
  registers : ℕ
  program : Program F (MatrixInput a b c) registers
  output : Fin a → Fin c → Fin registers

namespace MatrixAlgorithm

variable {F : Type*} [Field F] {a b c : ℕ}

def eval (P : MatrixAlgorithm F a b c)
    (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F) :
    Matrix (Fin a) (Fin c) F :=
  fun i k => P.program.eval (matrixInputs A B) (P.output i k)

def Correct (P : MatrixAlgorithm F a b c) : Prop :=
  ∀ (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F), P.eval A B = A * B

def cost (P : MatrixAlgorithm F a b c) : ℕ := P.program.cost

end MatrixAlgorithm

/-- Positive slack, one uniform constant, and a correct program at every size. -/
def AdmissibleExponent (F : Type*) [Field F] (τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm F n n n,
      P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (τ + ε)

def omega (F : Type*) [Field F] : ℝ := sInf {τ : ℝ | AdmissibleExponent F τ}

/-- The inner dimension of an `n × n^k` by `n^k × n` multiplication. -/
def innerSize (n : ℕ) (k : ℝ) : ℕ := ⌈(n : ℝ) ^ k⌉₊

def RectangularAdmissibleExponent (F : Type*) [Field F] (k τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm F n (innerSize n k) n,
      P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (τ + ε)

def rectangularOmega (F : Type*) [Field F] (k : ℝ) : ℝ :=
  sInf {τ : ℝ | RectangularAdmissibleExponent F k τ}

/-- The dual exponent is a supremum of exact exponent-two rectangular shapes. -/
def complexAlpha : ℝ :=
  sSup {k : ℝ | k ∈ Set.Icc 0 1 ∧ rectangularOmega ℂ k = 2}

end MatrixMultiplication.Arithmetic

end

namespace MatrixMultiplication

def complex_omega_le_nine_quarters_statement : Prop :=
  Arithmetic.omega ℂ ≤ (9 : ℝ) / 4

def complex_alpha_gt_93_div_200_statement : Prop :=
  (93 : ℝ) / 200 < Arithmetic.complexAlpha

def complex_rectangular_omega_lt_523_div_250_statement : Prop :=
  Arithmetic.rectangularOmega ℂ ((709 : ℝ) / 1000) < (523 : ℝ) / 250

end MatrixMultiplication

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.MatrixMultiplication.complex_omega_le_nine_quarters_statement ∧
  _root_.OAI.MatrixMultiplication.complex_alpha_gt_93_div_200_statement ∧
  _root_.OAI.MatrixMultiplication.complex_rectangular_omega_lt_523_div_250_statement

end Problem

/- Formalization scope, from lean/docs/107.md: The formalized results bound the complex matrix-multiplication exponent by $\omega(\mathbb C)\le9/4$, the dual exponent by $\alpha>0.465$, and the rectangular exponent at aspect ratio $0.709$ by $\omega(\mathbb C;1,0.709,1)<2.092$. The dual exponent is the supremum of rectangular aspect ratios attainable with exponent $2$. The arithmetic model counts additions, subtractions, and multiplications in finite division-free programs, with arbitrary positive exponent slack. The square bound implies the paper's weaker $2.258$ headline bound. The formalized result gives the unconditional bound $\omega(F)<2.371054886006746$ for every field $F$, including finite fields and fields of positive characteristic. The exponent counts additions, subtractions, and multiplications in finite division-free arithmetic programs, with arbitrary positive exponent slack. No numerical inequalities remain as hypotheses. The result concerns arithmetic complexity, rather than bit complexity or practical crossover sizes. -/
