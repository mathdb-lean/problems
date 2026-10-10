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

- problem_id: DimensionTenChannel
- collection: openai-math
- question_id: openai-math:272
- source: openai-math
- source_locator: lean/ComparatorChallenges/DimensionTenChannel.lean#OAI.DimensionTen.exists_channel_fin21
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs an entangled state on $`\mathbb C^{10}\otimes\mathbb C^{10}`$ with zero distillable secret key for the specified local-instrument protocols that complete almost surely. These allow joint local processing and authenticated two-way public communication, with no other shared private resource and an eavesdropper holding the input purification and public record. A trace-preserving PPT channel on $`M_{21}(\mathbb C)`$ whose square is not entanglement breaking disproves Christandl's PPT-square conjecture. ([Lean](lean/docs/272.md)) We construct an entangled state on $`\mathbb C^{10}\otimes\mathbb C^{10}`$ with zero distillable secret key for the local-instrument protocols specified here. They allow joint processing of all copies and unlimited two-way public communication, with the input as the only shared private resource and an eavesdropper holding a purification and the complete public record. The construction also disproves the unrestricted two-map PPT-composition conjecture. A separate trace-preserving PPT channel on $`M_{21}(\mathbb C)`$ has a square that is not entanglement breaking.
- notes: OpenAI math result family 272, Entanglement without distillable secret key -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/272.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.DimensionTen.exists_channel_fin21
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.Quantum.DimensionTen.Channel
- source_papers: preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf
- source_scope_note: lean/docs/272.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix

namespace ChannelCompletion

abbrev Mat (n : Type) := Matrix n n ℂ
abbrev Map (n m : Type) := Mat n →ₗ[ℂ] Mat m

variable {n m p : Type} [Fintype n] [Fintype m] [Fintype p]

def amplify (F : Map n m) {k : Type} (X : Mat (k × n)) : Mat (k × m) :=
  fun a b => F (fun i j => X (a.1, i) (b.1, j)) a.2 b.2

def CP (F : Map n m) : Prop :=
  ∀ (k : Type) [Fintype k] (X : Mat (k × n)), X.PosSemidef → (amplify F X).PosSemidef

def transposeMap : Map n n where
  toFun := Matrix.transpose
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def PPT (F : Map n m) : Prop := CP F ∧ CP (transposeMap.comp F)

def TracePreserving (F : Map n m) : Prop := ∀ X, Matrix.trace (F X) = Matrix.trace X

def Separable (Z : Mat (n × m)) : Prop :=
  ∃ (r : ℕ) (A : Fin r → Mat n) (B : Fin r → Mat m),
    (∀ i, (A i).PosSemidef) ∧ (∀ i, (B i).PosSemidef) ∧
    Z = ∑ i, A i ⊗ₖ B i

def EntanglementBreaking (F : Map n m) : Prop :=
  CP F ∧ ∀ (k : Type) [Fintype k] (X : Mat (k × n)),
    X.PosSemidef → Separable (amplify F X)

end ChannelCompletion

namespace DimensionTen

/-- A trace-preserving PPT channel on twenty-one dimensions with a non-entanglement-breaking square. -/
def exists_channel_fin21_statement : Prop :=
  ∃ Θ : ChannelCompletion.Map (Fin 21) (Fin 21),
      ChannelCompletion.PPT Θ ∧ ChannelCompletion.TracePreserving Θ ∧
        ¬ ChannelCompletion.EntanglementBreaking (Θ.comp Θ)

end DimensionTen

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.DimensionTen.exists_channel_fin21_statement

end Problem

/- Formalization scope, from lean/docs/272.md: The paper's entanglement construction yields counterexamples to PPT-composition claims. The linked formalization covers these consequences: two explicitly specified PPT maps on $10\times10$ complex matrices have a composition that is not entanglement breaking, and the nonzero Choi matrix of that composition has no nonzero product vector in its range. A separate trace-preserving PPT channel on $21\times21$ matrices has a square that is not entanglement breaking. The paper's zero-distillable-secret-key statement is outside these two selected Comparator statements. -/
