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

- problem_id: RegularParity
- collection: openai-math
- question_id: openai-math:274
- source: openai-math
- source_locator: lean/ComparatorChallenges/RegularParity.lean#OAI.QAC.parity_lower_bound_polynomial_size
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves Moore's parity conjecture in the measured-output model: constant-depth quantum circuits with arbitrary one-qubit gates, unbounded-arity Toffoli gates and polynomially many total qubits cannot compute parity with any fixed positive worst-case advantage. Ancillas start in zero, one output qubit is measured, and all other registers may be discarded. Xu–Li's reductions give the same bounded-error obstruction for strict majority. ([Lean](lean/docs/274.md)) We prove that constant-depth quantum circuits with arbitrary one-qubit and unbounded-arity Toffoli gates cannot compute parity with any fixed positive worst-case advantage using polynomially many qubits. Ancillas start in zero, only one output qubit is measured, and all final garbage is unrestricted. This resolves Moore's parity conjecture in the measured-output model. We prove that constant-depth quantum circuits with arbitrary one-qubit gates and unbounded-arity Toffoli gates cannot compute parity with any fixed positive worst-case advantage using polynomially many total qubits. Ancillary qubits are initialized to $`|0\rangle`$, one output qubit is measured, and all other final registers may be discarded without restriction. This resolves Moore's parity conjecture in the measured-output model.
- notes: OpenAI math result family 274, Parity is not in QAC<sup>0</sup> -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/274.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.QAC.parity_lower_bound_polynomial_size
- source_theorem_count: 1
- source_solution_module: OAI.InformationTheory.QuantumCircuit.Main
- source_main_result: OAI.QAC.parity_lower_bound_polynomial_size
- source_papers: preprints/Product-projection-localization-and-the-QAC0-parity-lower-bound-September-24-2026/paper.pdf preprints/Regular-trajectories-pruning-and-quantum-parity-September-24-2026/paper.pdf
- source_scope_note: lean/docs/274.md
- source_field: InformationTheory
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace QAC

abbrev Bit := Fin 2
abbrev Word (N : ℕ) := Fin N → Bit
abbrev Operator (N : ℕ) := Matrix (Word N) (Word N) ℂ
abbrev QubitOperator := Matrix Bit Bit ℂ

/-- Tensor product in the computational basis. -/
def tensorMatrix {N : ℕ} (a : Fin N → QubitOperator) : Operator N :=
  fun x y => ∏ i, a i (x i) (y i)

/-- A one-qubit unitary or an unbounded-arity Toffoli gate. -/
inductive Gate (N : ℕ) where
  | local (q : Fin N) (u : Matrix.unitaryGroup Bit ℂ)
  | toffoli (controls : Finset (Fin N)) (target : Fin N) (hne : target ∉ controls)

namespace Gate

def support {N : ℕ} : Gate N → Finset (Fin N)
  | .local q _ => {q}
  | .toffoli c t _ => insert t c

/-- A Toffoli flips its target iff all controls are one. -/
def toffoliWord {N : ℕ} (c : Finset (Fin N)) (t : Fin N) (x : Word N) : Word N :=
  if ∀ i ∈ c, x i = 1 then Function.update x t (1 - x t) else x

def matrix {N : ℕ} : Gate N → Operator N
  | .local q u => tensorMatrix fun i => if i = q then (u : QubitOperator) else 1
  | .toffoli c t _ => fun x y => if x = toffoliWord c t y then 1 else 0

end Gate

structure PhysicalLayer (N : ℕ) where
  gates : List (Gate N)
  disjoint : gates.Pairwise (fun A B => Disjoint A.support B.support)

def physicalLayerMatrix {N : ℕ} (L : PhysicalLayer N) : Operator N :=
  (L.gates.map Gate.matrix).prod

/-- Chronological order: the rightmost matrix acts first. -/
def physicalCircuitMatrix {N : ℕ} (layers : List (PhysicalLayer N)) : Operator N :=
  ((layers.map physicalLayerMatrix).reverse).prod

/-- The computational-basis input with the remaining qubits initialized to zero. -/
def inputWord {n N : ℕ} (x : Word n) : Word N :=
  fun i => if h : i.val < n then x ⟨i.val, h⟩ else 0

def parity {n : ℕ} (x : Word n) : Bit := ∑ i, x i

/-- Born probability, summing all final garbage with no cleanliness assumption. -/
def successProbability {n N : ℕ} (W : Operator N) (out : Fin N) (x : Word n) : ℝ :=
  ∑ y : Word N, if y out = parity x then Complex.normSq (W y (inputWord x)) else 0

/-- Fixed-depth circuits with polynomially many total qubits cannot compute parity
with worst-case success at least two thirds. -/
def parity_lower_bound_polynomial_size_statement : Prop :=
  ∀ (d k C : ℕ) (_hd : 0 < d) (_hk : 0 < k) (_hC : 0 < C),
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ N : ℕ, n ≤ N → N ≤ C * (n + 1) ^ k →
      ∀ layers : List (PhysicalLayer N), layers.length ≤ d →
        ∀ out : Fin N, ∃ x : Word n,
          successProbability (physicalCircuitMatrix layers) out x < (2 : ℝ) / 3

end QAC

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.QAC.parity_lower_bound_polynomial_size_statement

end Problem

/- Formalization scope, from lean/docs/274.md: The formalization rules out bounded-error parity computation by constant-depth quantum circuits with polynomially many zero-initialized ancillary qubits. For every fixed depth, polynomial bound on the total number of qubits, and $0<\varepsilon\le1/2$, every sufficiently large input length has an input on which the measured-output parity success probability is less than $1/2+\varepsilon$. A companion specialization gives success strictly below $2/3$. The formalization also includes the product-projection localization estimate supporting this bound. The formalized result supplies the polynomial-size parity consequence of the paper. For every fixed circuit depth and polynomial bound on the number of qubits, all sufficiently large input lengths have an input on which any such circuit computes measured-output parity with probability strictly below $2/3$. Ancillary qubits start at zero. The formalization also contains the general positive-advantage parity bound and its product-projection localization estimate; regular-trajectory propagation and pruning are not separate formalized statements here. -/
