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

- problem_id: UniversalFInfinity
- collection: openai-math
- question_id: openai-math:250
- source: openai-math
- source_locator: lean/ComparatorChallenges/UniversalFInfinity.lean#OAI.UniversalFInfinity.universal_group_of_type_FInfinity
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: A finitely generated group has decidable word problem exactly when it embeds in a finitely presented simple group, proving the Boone–Higman conjecture. The target can have type F∞: a classifying space with finitely many cells in each dimension. A single group of type F∞ can also contain every finitely presented group. ([Lean](lean/docs/250.md)) We prove the Boone–Higman conjecture. A finitely generated group has decidable word problem if and only if it embeds in a finitely presented simple group. Every finitely generated group with decidable word problem embeds in a simple group of type F∞. This resolves the higher-finiteness strengthening of the Boone–Higman conjecture. We construct a single group of type F∞ containing every finitely presented group. Its finitely generated subgroups, up to isomorphism, are exactly the finitely generated recursively presented groups. This answers the F∞ form of the higher-dimensional Higman embedding question.
- notes: OpenAI math result family 250, Boone–Higman embeddings with higher finiteness -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/250.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.UniversalFInfinity.universal_group_of_type_FInfinity
- source_theorem_count: 1
- source_solution_module: OAI.GroupTheory.UniversalGroup.Main
- source_main_result: OAI.UniversalFInfinity.universal_group_of_type_FInfinity
- source_papers: preprints/Finite-algebraic-envelopes-and-the-Boone-Higman-conjecture-September-23-2026/paper.pdf preprints/Simple-F-infinity-overgroups-of-groups-with-decidable-word-problem-September-23-2026/paper.pdf preprints/A-universal-group-of-type-F-infinity-September-23-2026/paper.pdf
- source_scope_note: lean/docs/250.md
- source_field: GroupTheory
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace UniversalFInfinity
universe u

def HasTypeFInfinity (G : Type u) [Group G] : Prop :=
  ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X)
    (_ : ConnectedSpace X) (cw : Topology.CWComplex (Set.univ : Set X)),
    (∀ n : ℕ, Finite (cw.cell n)) ∧
    (∃ x : X, Nonempty (FundamentalGroup X x ≃* G)) ∧
    ∃ (E : Type u) (_ : TopologicalSpace E) (_ : ContractibleSpace E)
      (p : E → X), Function.Surjective p ∧ IsCoveringMap p

def universal_group_of_type_FInfinity_statement : Prop :=
  ∃ (H : Type u) (groupH : Group H),
      @HasTypeFInfinity H groupH ∧
      ∀ (G : Type u) [Group G] [Group.IsFinitelyPresented G],
        ∃ φ : G →* H, Function.Injective φ

end UniversalFInfinity

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.UniversalFInfinity.universal_group_of_type_FInfinity_statement.{u}

end Problem

/- Formalization scope, from lean/docs/250.md: The Boone–Higman conjecture characterizes finitely generated groups with decidable word problem by embeddings into finitely presented simple groups. The formalization proves the equivalence in full: a finitely generated group has a computable word problem for a finite generating set exactly when it embeds by an injective homomorphism into a finitely presented simple group. The formalization proves the higher-finiteness strengthening of the Boone–Higman conjecture: every finitely generated group with decidable word problem embeds by an injective homomorphism into a nontrivial simple group of type $F_\infty$. Here type $F_\infty$ means that the group has a classifying CW complex with finitely many cells in each dimension. No additional finiteness property of the original group is assumed. The formalized result constructs one group $H$ of type $F_\infty$ containing every finitely presented group. Here type $F_\infty$ means that $H$ has a classifying space with finitely many cells in each dimension. The group $H$ is fixed before the groups embedded into it are chosen. No word-problem assumption is imposed, and the classifying space need not be finite-dimensional or have finitely many cells in total. The paper's converse about recursively presented subgroups is not included. -/
