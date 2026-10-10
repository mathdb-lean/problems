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

- problem_id: DepthFive
- collection: openai-math
- question_id: openai-math:135
- source: openai-math
- source_locator: lean/ComparatorChallenges/DepthFive.lean#OAI.Problem335.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Over every characteristic-zero field, the $`(1,1)`$ entry of a product of n independent $`n\times n`$ variable matrices requires $`n^{\Theta(\sqrt n)}`$ gates in homogeneous depth-five sum–product circuits. This sharp bound allows shared gates and bottom linear forms involving all variables. ([Lean](lean/docs/135.md)) Let $`\mathop{\mathrm{IMM}}\nolimits _{n,n}`$ be the $`(1,1)`$ entry of a product of n independent $`n\times n`$ matrices of variables. Over every field of characteristic zero, every syntactically homogeneous $`\Sigma\Pi\Sigma\Pi\Sigma`$ circuit computing $`\mathop{\mathrm{IMM}}\nolimits _{n,n}`$ has at least $`n^{\sqrt n/400}`$ gates for all sufficiently large n, with an absolute threshold independent of the field. Bottom linear forms may have arbitrary support, and arbitrary finite fan-in, fan-out, and gate sharing are allowed. Over every field, a block expansion gives such circuits with at most $`n^{\sqrt n+4}`$ gates for n ≥ 2. Thus the gate complexity over characteristic-zero fields is $`n^{\Theta(\sqrt n)}`$.
- notes: OpenAI math result family 135, Homogeneous depth-five lower bounds for iterated matrix multiplication -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/135.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Problem335.main
- source_theorem_count: 1
- source_solution_module: OAI.Algebra.DepthFive.Bounds
- source_papers: preprints/Homogeneous-depth-five-lower-bounds-for-iterated-matrix-multiplication-September-25-2026/Homogeneous-depth-five-lower-bounds-for-iterated-matrix-multiplication-September-25-2026.pdf
- source_scope_note: lean/docs/135.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open scoped BigOperators
universe u

namespace Problem335

inductive D5Leaf (K : Type u) (n : ℕ) where
  | scalar : K → D5Leaf K n
  | variable : (Fin n × Fin n × Fin n) → D5Leaf K n

def d5LeafDegree {K : Type u} {n : ℕ} : D5Leaf K n → ℕ
  | D5Leaf.scalar _ => 0
  | D5Leaf.variable _ => 1

structure Depth5Circuit (K : Type u) [CommSemiring K] (n : ℕ) where
  leafCount : ℕ
  leaves : Fin leafCount → D5Leaf K n
  bottomCount : ℕ
  bottomInputs : Fin bottomCount → List (K × Fin leafCount)
  bottomDegree : Fin bottomCount → ℕ
  bottomHomogeneous :
    ∀ i entry, entry ∈ bottomInputs i → d5LeafDegree (leaves entry.2) = bottomDegree i
  bottomEmpty :
    ∀ i, bottomInputs i = [] → bottomDegree i = 0
  lowerCount : ℕ
  lowerInputs : Fin lowerCount → List (Fin bottomCount)
  middleCount : ℕ
  middleInputs : Fin middleCount → List (K × Fin lowerCount)
  middleDegree : Fin middleCount → ℕ
  middleHomogeneous :
    ∀ i entry, entry ∈ middleInputs i →
      ((lowerInputs entry.2).map bottomDegree).sum = middleDegree i
  middleEmpty :
    ∀ i, middleInputs i = [] → middleDegree i = 0
  upperCount : ℕ
  upperInputs : Fin upperCount → List (Fin middleCount)
  outputInputs : List (K × Fin upperCount)
  outputDegree : ℕ
  outputHomogeneous :
    ∀ entry, entry ∈ outputInputs →
      ((upperInputs entry.2).map middleDegree).sum = outputDegree
  outputEmpty :
    outputInputs = [] → outputDegree = 0

def d5LeafValue {K : Type u} [CommSemiring K] {n : ℕ}
    (x : D5Leaf K n) : MvPolynomial (Fin n × Fin n × Fin n) K :=
  match x with
  | D5Leaf.scalar a => MvPolynomial.C a
  | D5Leaf.variable i => MvPolynomial.X i

def bottomValue {K : Type u} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (i : Fin c.bottomCount) :
    MvPolynomial (Fin n × Fin n × Fin n) K := by
  classical
  exact ((c.bottomInputs i).map (fun entry =>
    MvPolynomial.C entry.1 * d5LeafValue (c.leaves entry.2))).sum

def lowerValue {K : Type u} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (i : Fin c.lowerCount) :
    MvPolynomial (Fin n × Fin n × Fin n) K := by
  classical
  exact ((c.lowerInputs i).map (fun j => bottomValue c j)).prod

def middleValue {K : Type u} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (i : Fin c.middleCount) :
    MvPolynomial (Fin n × Fin n × Fin n) K := by
  classical
  exact ((c.middleInputs i).map (fun entry =>
    MvPolynomial.C entry.1 * lowerValue c entry.2)).sum

def upperValue {K : Type u} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (i : Fin c.upperCount) :
    MvPolynomial (Fin n × Fin n × Fin n) K := by
  classical
  exact ((c.upperInputs i).map (fun j => middleValue c j)).prod

def circuitValue {K : Type u} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) : MvPolynomial (Fin n × Fin n × Fin n) K := by
  classical
  exact (c.outputInputs.map (fun entry =>
    MvPolynomial.C entry.1 * upperValue c entry.2)).sum

def circuitSize {K : Type u} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) : ℕ :=
  c.leafCount + c.bottomCount + c.lowerCount + c.middleCount + c.upperCount + 1

def immLayer (K : Type u) [CommSemiring K] (n : ℕ) (t : Fin n) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n × Fin n) K) :=
  fun i j => MvPolynomial.X (t, i, j)

def imm (K : Type u) [CommSemiring K] (n : ℕ) :
    MvPolynomial (Fin n × Fin n × Fin n) K := by
  classical
  by_cases h : 0 < n
  · let matrices :
        List (Matrix (Fin n) (Fin n)
          (MvPolynomial (Fin n × Fin n × Fin n) K)) :=
      List.ofFn (fun t : Fin n => immLayer K n t)
    exact matrices.prod ⟨0, h⟩ ⟨0, h⟩
  · exact 0

def ceilSqrt (n : ℕ) : ℕ :=
  Nat.sqrt n + if (Nat.sqrt n) ^ 2 = n then 0 else 1

def ceilDiv (n t : ℕ) : ℕ :=
  (n + t - 1) / t

def upperGateBound (n : ℕ) : ℕ :=
  let t := ceilSqrt n
  let r := ceilDiv n t
  2 * n ^ 3 + r * n ^ 2 + r * n ^ (t + 1) + n ^ (r - 1) + 1

def main_statement : Prop :=
  (∃ threshold : ℕ, ∀ size : ℕ, threshold ≤ size →
      ∀ circuit : Depth5Circuit ℂ size, circuitValue circuit = imm ℂ size →
        (size : ℝ) ^ (Real.sqrt (size : ℝ) / 400) ≤ (circuitSize circuit : ℝ)) ∧
    (∃ threshold : ℕ, ∀ (FieldType : Type u) [Field FieldType] [CharZero FieldType],
      ∀ size : ℕ, threshold ≤ size → ∀ circuit : Depth5Circuit FieldType size,
        circuitValue circuit = imm FieldType size →
          (size : ℝ) ^ (Real.sqrt (size : ℝ) / 400) ≤ (circuitSize circuit : ℝ)) ∧
    (∀ (FieldType : Type u) [Field FieldType] (size : ℕ), 2 ≤ size →
      ∃ circuit : Depth5Circuit FieldType size, circuitValue circuit = imm FieldType size ∧
        circuitSize circuit ≤ upperGateBound size ∧
        (upperGateBound size : ℝ) ≤ (size : ℝ) ^ (Real.sqrt (size : ℝ) + 4))

end Problem335

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.Problem335.main_statement.{u}

end Problem

/- Formalization scope, from lean/docs/135.md: Let $\mathrm{IMM}_{n,n}$ be the $(1,1)$ entry of the product of $n$ independent $n\times n$ variable matrices. The formalization proves that, over every characteristic-zero field, syntactically homogeneous depth-five $\Sigma\Pi\Sigma\Pi\Sigma$ circuits computing this polynomial require at least $n^{\sqrt n/400}$ gates for all sufficiently large $n$, with a threshold independent of the field. Arbitrary bottom support, finite fan-in and fan-out, and sharing are allowed. It also gives, over every field and for $n\ge2$, circuits with at most $n^{\sqrt n+4}$ gates. These are the lower and upper bounds selected from the paper. -/
