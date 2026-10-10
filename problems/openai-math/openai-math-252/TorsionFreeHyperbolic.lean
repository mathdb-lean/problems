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

- problem_id: TorsionFreeHyperbolic
- collection: openai-math
- question_id: openai-math:252
- source: openai-math
- source_locator: lean/ComparatorChallenges/TorsionFreeHyperbolic.lean#OAI.Release075.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs a torsion-free word-hyperbolic group that is not residually finite, answering the residual-finiteness question negatively. One fixed nonidentity element is killed by every finite-dimensional linear representation over every commutative field, so the group is not linear over any such field. ([Lean](lean/docs/252.md)) We construct a torsion-free word-hyperbolic group that is not residually finite, answering the residual-finiteness question for hyperbolic groups negatively.
- notes: OpenAI math result family 252, A torsion-free hyperbolic group that is neither residually finite nor linear over any field -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/252.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Release075.main
- source_theorem_count: 1
- source_solution_module: OAI.GroupTheory.Hyperbolic.Main
- source_main_result: OAI.Release075.main
- source_papers: preprints/a-torsion-free-hyperbolic-group-that-is-not-residually-finite-September-23-2026/paper.pdf
- source_scope_note: lean/docs/252.md
- source_field: GroupTheory
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace Release075

universe u v

/-- No nonidentity element has finite order. This does not assert unique roots. -/
def TorsionFree (G : Type u) [Group G] : Prop :=
  ∀ (g : G) (n : ℕ), 0 < n → g ^ n = 1 → g = 1

/-- A shortest edge path in the unit-edge graph. -/
def Geodesic {V : Type u} (X : SimpleGraph V) {x y : V} (p : X.Walk x y) : Prop :=
  p.length = X.dist x y

/-- Each vertex of `p` is within `δ` of a vertex of `q` or `r`. -/
def SideThin {V : Type u} (X : SimpleGraph V) (δ : ℕ) {x y z : V}
    (p : X.Walk x y) (q : X.Walk y z) (r : X.Walk z x) : Prop :=
  ∀ a ∈ p.support, ∃ b, (b ∈ q.support ∨ b ∈ r.support) ∧ X.dist a b ≤ δ

/-- A finitely generated group with a unit-edge Cayley graph whose geodesic triangles
are uniformly thin. Connectedness of this Cayley graph asserts that `S` generates. -/
def WordHyperbolic (G : Type u) [Group G] : Prop :=
  ∃ S : Set G, S.Finite ∧ (SimpleGraph.mulCayley S).Connected ∧
    ∃ δ : ℕ, ∀ (x y z : G)
      (p : (SimpleGraph.mulCayley S).Walk x y)
      (q : (SimpleGraph.mulCayley S).Walk y z)
      (r : (SimpleGraph.mulCayley S).Walk z x),
      Geodesic (SimpleGraph.mulCayley S) p →
      Geodesic (SimpleGraph.mulCayley S) q →
      Geodesic (SimpleGraph.mulCayley S) r →
      SideThin (SimpleGraph.mulCayley S) δ p q r ∧
      SideThin (SimpleGraph.mulCayley S) δ q r p ∧
      SideThin (SimpleGraph.mulCayley S) δ r p q

def main_statement : Prop :=
  ∃ (G : Type) (_ : Group G),
    TorsionFree G ∧ WordHyperbolic G ∧ ¬ Group.ResiduallyFinite G

end Release075

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Release075.main_statement

end Problem

/- Formalization scope, from lean/docs/252.md: The residual-finiteness question for hyperbolic groups asks whether every nonidentity element survives in some finite quotient. The formalized result gives a negative answer by constructing a torsion-free word-hyperbolic group that is not residually finite. Nonlinearity over every field is not a separate conclusion of the statement linked below. -/
