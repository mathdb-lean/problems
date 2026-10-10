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

- problem_id: DimensionTenPair
- collection: openai-math
- question_id: openai-math:272
- source: openai-math
- source_locator: lean/ComparatorChallenges/DimensionTenPair.lean#OAI.DimensionTen.main_pair
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs an entangled state on $`\mathbb C^{10}\otimes\mathbb C^{10}`$ with zero distillable secret key for the specified local-instrument protocols that complete almost surely. These allow joint local processing and authenticated two-way public communication, with no other shared private resource and an eavesdropper holding the input purification and public record. A trace-preserving PPT channel on $`M_{21}(\mathbb C)`$ whose square is not entanglement breaking disproves Christandl's PPT-square conjecture. ([Lean](lean/docs/272.md)) We construct an entangled state on $`\mathbb C^{10}\otimes\mathbb C^{10}`$ with zero distillable secret key for the local-instrument protocols specified here. They allow joint processing of all copies and unlimited two-way public communication, with the input as the only shared private resource and an eavesdropper holding a purification and the complete public record. The construction also disproves the unrestricted two-map PPT-composition conjecture. A separate trace-preserving PPT channel on $`M_{21}(\mathbb C)`$ has a square that is not entanglement breaking.
- notes: OpenAI math result family 272, Entanglement without distillable secret key -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/272.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.DimensionTen.main_pair
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.Quantum.DimensionTen.Main
- source_papers: preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf
- source_scope_note: lean/docs/272.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
open scoped Matrix ComplexOrder
open Matrix Complex
namespace DimensionTen

def blocksZ : Fin 4 → Matrix (Fin 6) (Fin 4) ℤ :=
  ![ ![ ![6,0,0,0], ![0,6,0,0], ![0,0,6,0], ![0,0,0,6], ![0,0,0,0], ![0,0,0,0] ],
     ![ ![-12,0,0,0], ![0,-6,0,0], ![0,0,6,0], ![0,0,0,12], ![-6,0,6,6], ![-6,-6,6,0] ],
     ![ ![0,6,-2,0], ![6,6,0,2], ![-2,0,10,0], ![0,2,0,24], ![0,0,0,6], ![0,-6,6,-6] ],
     ![ ![0,0,-4,-3], ![0,-2,-3,-4], ![-4,-3,11,6], ![-3,-4,6,25], ![6,6,0,0], ![0,-6,6,6] ] ]

def blocks (i : Fin 4) : Matrix (Fin 6) (Fin 4) ℂ :=
  (blocksZ i).map (Int.castRingHom ℂ)

def pencilMap (A : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ i : Fin 4, ∑ j : Fin 4, A i j • ((blocks i)ᵀ * blocks j)

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def IsComplexLinear {a b : ℕ} (F : Mat a → Mat b) : Prop :=
  (∀ A B, F (A + B) = F A + F B) ∧
  (∀ (c : ℂ) A, F (c • A) = c • F A)

def amplify {a b : ℕ} (F : Mat a → Mat b) (k : ℕ)
    (X : Matrix (Fin k × Fin a) (Fin k × Fin a) ℂ) :
    Matrix (Fin k × Fin b) (Fin k × Fin b) ℂ :=
  fun u v => F (fun i j => X (u.1, i) (v.1, j)) u.2 v.2

def CompletelyPositive {a b : ℕ} (F : Mat a → Mat b) : Prop :=
  ∀ k : ℕ, 0 < k → ∀ X : Matrix (Fin k × Fin a) (Fin k × Fin a) ℂ,
    X.PosSemidef → (amplify F k X).PosSemidef

def PPT {a b : ℕ} (F : Mat a → Mat b) : Prop :=
  IsComplexLinear F ∧ CompletelyPositive F ∧
    CompletelyPositive (fun X => (F X)ᵀ)

def separable {a b : ℕ} (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) : Prop :=
  ∃ r : ℕ, ∃ A : Fin r → Mat a, ∃ B : Fin r → Mat b,
    (∀ i, (A i).PosSemidef ∧ (B i).PosSemidef) ∧
    X = ∑ i, Matrix.kronecker (A i) (B i)

def EntanglementBreaking {a b : ℕ} (F : Mat a → Mat b) : Prop :=
  CompletelyPositive F ∧
  ∀ k : ℕ, 0 < k → ∀ X : Matrix (Fin k × Fin a) (Fin k × Fin a) ℂ,
    X.PosSemidef → separable (amplify F k X)

def choi {a b : ℕ} (F : Mat a → Mat b) :
    Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ :=
  fun u v => F (Matrix.single u.1 v.1 1) u.2 v.2

def tensorMap {a b c d : ℕ} (F : Mat a → Mat b) (G : Mat c → Mat d)
    (X : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ) :
    Matrix (Fin b × Fin d) (Fin b × Fin d) ℂ :=
  ∑ i : Fin c, ∑ j : Fin c,
    Matrix.kronecker (F (fun a b => X (a, i) (b, j))) (G (Matrix.single i j 1))

def hsAdjoint {a b : ℕ} (F : Mat a → Mat b) (Y : Mat b) : Mat a :=
  fun i j => ∑ u : Fin b, ∑ v : Fin b, star (F (Matrix.single i j 1) u v) * Y u v

def symmetricPairs : Fin 10 → Fin 4 × Fin 4 :=
  ![(0,0), (0,1), (0,2), (0,3), (1,1), (1,2), (1,3), (2,2), (2,3), (3,3)]

def exteriorPairs : Fin 6 → Fin 4 × Fin 4 :=
  ![(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]

def symmetricIsometry : Matrix (Fin 4 × Fin 4) (Fin 10) ℂ :=
  fun ij a =>
    let p := (symmetricPairs a).1
    let q := (symmetricPairs a).2
    if p = q then (if ij = (p,p) then 1 else 0)
    else ((if ij = (p,q) then 1 else 0) + (if ij = (q,p) then 1 else 0)) /
      (Real.sqrt 2 : ℂ)

def exteriorIsometry : Matrix (Fin 4 × Fin 4) (Fin 6) ℂ :=
  fun ij a =>
    let p := (exteriorPairs a).1
    let q := (exteriorPairs a).2
    ((if ij = (p,q) then 1 else 0) - (if ij = (q,p) then 1 else 0)) /
      (Real.sqrt 2 : ℂ)

def hodgeComplement : Mat 6 :=
  ![ ![0,0,0,0,0,1], ![0,0,0,0,-1,0], ![0,0,0,1,0,0],
     ![0,0,1,0,0,0], ![0,-1,0,0,0,0], ![1,0,0,0,0,0] ]

def firstSix : Matrix (Fin 10) (Fin 6) ℂ :=
  fun i j => if i.val = j.val then 1 else 0

def exteriorMap (A : Mat 10) : Mat 6 :=
  exteriorIsometryᴴ *
    tensorMap pencilMap pencilMap (symmetricIsometry * A * symmetricIsometryᴴ) *
      exteriorIsometry

def complementaryMap (A : Mat 10) : Mat 6 :=
  hodgeComplement * (exteriorMap A)ᵀ * hodgeComplementᴴ

def phiOne (A : Mat 10) : Mat 10 :=
  firstSix * exteriorMap Aᵀ * firstSixᴴ

def phiTwo (B : Mat 10) : Mat 10 :=
  hsAdjoint complementaryMap (firstSixᴴ * B * firstSix)

def compositeChoi : Matrix (Fin 10 × Fin 10) (Fin 10 × Fin 10) ℂ :=
  choi (phiTwo ∘ phiOne)

def productVector {a b : ℕ} (u : Fin a → ℂ) (v : Fin b → ℂ) : Fin a × Fin b → ℂ :=
  fun ij => u ij.1 * v ij.2

def main_pair_statement : Prop :=
  ∃ Φ₁ Φ₂ : Mat 10 → Mat 10,
      Φ₁ = phiOne ∧ Φ₂ = phiTwo ∧ PPT Φ₁ ∧ PPT Φ₂ ∧
      (let Z := choi (Φ₂ ∘ Φ₁)
       Z ≠ 0 ∧
       (∀ u v : Fin 10 → ℂ, ∀ w : Fin 10 × Fin 10 → ℂ,
         Z *ᵥ w = productVector u v → u = 0 ∨ v = 0) ∧
       ¬ EntanglementBreaking (Φ₂ ∘ Φ₁))

end DimensionTen
end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.DimensionTen.main_pair_statement

end Problem

/- Formalization scope, from lean/docs/272.md: The paper's entanglement construction yields counterexamples to PPT-composition claims. The linked formalization covers these consequences: two explicitly specified PPT maps on $10\times10$ complex matrices have a composition that is not entanglement breaking, and the nonzero Choi matrix of that composition has no nonzero product vector in its range. A separate trace-preserving PPT channel on $21\times21$ matrices has a square that is not entanglement breaking. The paper's zero-distillable-secret-key statement is outside these two selected Comparator statements. -/
