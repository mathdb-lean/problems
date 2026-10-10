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

- problem_id: MUBSix
- collection: openai-math
- question_id: openai-math:266
- source: openai-math
- source_locator: lean/ComparatorChallenges/MUBSix.lean#OAI.MUB6.fourier_and_family_bound
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves $`N(6)=3`$, resolving Zauner's dimension-six mutually unbiased bases conjecture: three such bases exist in ℂ6, but four cannot. The exclusion is a complete certified computation under the stated binary64 arithmetic and compiler conditions. An independent companion proves the Matolcsi–Ruzsa–Weiner Fourier-vanishing conjecture for order-six complex Hadamard matrices outside Tao's cubic equivalence class. ([Lean](lean/docs/266.md)) We prove that the maximum number of mutually unbiased orthonormal bases in ℂ6 is three, resolving Zauner's dimension-six MUB conjecture. The upper bound is computer-assisted: under the stated binary64 arithmetic and compiler conditions, a complete execution of the documented verification pipeline excludes four arbitrary complex bases. We prove the Fourier-vanishing conjecture of Matolcsi, Ruzsa, and Weiner: every complex Hadamard matrix of order six outside Tao's cubic equivalence class has a vanishing character sum at every permutation of $`(1,1,1,-1,-1,-1)`$. We also give an exact certificate excluding seven mutually unbiased bases in ℂ6; by Weiner's completion theorem, this yields an upper bound of five. Both certificates use only integer and rational arithmetic, and the complete verifier is included.
- notes: OpenAI math result family 266, Exactly three mutually unbiased bases in dimension six -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/266.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.MUB6.fourier_and_family_bound
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.MutuallyUnbiased.Main
- source_papers: preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf preprints/Exact-Fourier-certificates-for-complex-Hadamard-matrices-of-order-six-September-24-2026/Exact-Fourier-certificates-for-complex-Hadamard-matrices-of-order-six-September-24-2026.pdf
- source_scope_note: lean/docs/266.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

abbrev Coord := Fin 6
abbrev CMatrix := Matrix Coord Coord ℂ
abbrev Charge := Coord → ℤ

def IsHadamard (H : CMatrix) : Prop :=
  (∀ i j, Complex.normSq (H i j) = 1) ∧
  H.conjTranspose * H = (6 : ℂ) • (1 : CMatrix)

def character (x : Coord → ℂ) (a : Charge) : ℂ := ∏ i, x i ^ a i

def g (H : CMatrix) (a : Charge) : ℂ :=
  (6 : ℂ)⁻¹ * ∑ k, character (fun i => H i k) a

def alpha : Charge := ![1, 1, 1, -1, -1, -1]

def permuteCharge (π : Equiv.Perm Coord) (a : Charge) : Charge := a ∘ π

/-- Full Hadamard equivalence, with arbitrary unit complex phases. -/
def Equivalent (H K : CMatrix) : Prop :=
  ∃ (r c : Equiv.Perm Coord) (u v : Coord → ℂ),
    (∀ i, Complex.normSq (u i) = 1) ∧ (∀ j, Complex.normSq (v j) = 1) ∧
    ∀ i j, K i j = u i * H (r i) (c j) * v j

def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

/-- The five-cycle exponent matrix in equation (cubic-matrix).
The entries 2 represent the exponents -1 modulo three. -/
def taoExponent : Matrix Coord Coord ℕ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 1, 2, 2, 1;
     0, 1, 0, 1, 2, 2;
     0, 2, 1, 0, 1, 2;
     0, 2, 2, 1, 0, 1;
     0, 1, 2, 2, 1, 0]

def tao : CMatrix := fun i j => omega ^ taoExponent i j

abbrev Space := EuclideanSpace ℂ Coord
abbrev Basis := OrthonormalBasis Coord ℂ Space

def IsMUBFamily {n : ℕ} (B : Fin n → Basis) : Prop :=
  ∀ r s, r ≠ s → ∀ i j,
    Complex.normSq (inner ℂ (B r i) (B s j)) = (1 : ℝ) / 6

def Attainable (n : ℕ) : Prop := ∃ B : Fin n → Basis, IsMUBFamily B

def fourier_and_family_bound_statement : Prop :=
  (∀ H : CMatrix, IsHadamard H → ¬Equivalent H tao →
      ∀ π : Equiv.Perm Coord, g H (permuteCharge π alpha) = 0) ∧
    (∀ n : ℕ, Attainable n → n ≤ 5)

end MUB6

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.MUB6.fourier_and_family_bound_statement

end Problem

/- Formalization scope, from lean/docs/266.md: The paper claims that at most three mutually unbiased orthonormal bases exist in $\mathbb C^6$. The linked formalization proves a weaker family bound: every family in its mutually unbiased bases model has at most five members. It also proves a Fourier character-sum vanishing statement for order-six complex Hadamard matrices not equivalent to the Tao matrix, uniformly over coordinate permutations. The selected statement does not establish the paper's upper bound of three or its computer-assisted exclusion of four arbitrary bases. The linked formalization proves a cancellation lemma used in the order-six complex Hadamard analysis. Let $H$ and its entrywise square both be complex Hadamard matrices, and fix two distinct rows. If the cubes of their six entrywise ratios take only two distinct values, then the sum of the row-ratio terms over either specified cube fiber is zero. This is a supporting Fourier cancellation statement. The paper's full character-sum vanishing theorem and its mutually unbiased bases bound are outside this selected statement. -/
