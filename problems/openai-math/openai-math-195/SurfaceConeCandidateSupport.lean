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

- problem_id: SurfaceConeCandidateSupport
- collection: openai-math
- question_id: openai-math:195
- source: openai-math
- source_locator: lean/ComparatorChallenges/SurfaceConeCandidateSupport.lean#OAI.SmallCM.candidate_ring_properties
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs a three-dimensional complete Noetherian normal local domain over ℂ with no nonzero finitely generated maximal Cohen–Macaulay module. A three-dimensional local domain essentially of finite type over ℂ has the same property, disproving the domain form of the small Cohen–Macaulay module conjecture. ([Lean](lean/docs/195.md)) We construct a three-dimensional complete Noetherian normal local domain containing ℂ, with residue field ℂ, that has no nonzero finitely generated maximal Cohen–Macaulay module. This disproves the domain form of the small Cohen–Macaulay module conjecture.
- notes: OpenAI math result family 195, A counterexample to the small Cohen–Macaulay module conjecture -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/195.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.SmallCM.candidate_ring_properties
- source_theorem_count: 1
- source_solution_module: OAI.AlgebraicGeometry.SurfaceCones.CandidateRing
- source_main_result: OAI.SmallCM.candidate_ring_properties
- source_papers: preprints/A-Complete-Local-Domain-Without-a-Small-Cohen-Macaulay-Module-September-23-2026/paper.pdf
- source_scope_note: lean/docs/195.md
- source_field: AlgebraicGeometry
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace SmallCM

/-- Ring-theoretic properties of the completed surface cone. -/
def candidate_ring_properties_statement : Prop :=
  ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsNoetherianRing R)
      (_ : IsIntegrallyClosed R) (_ : IsLocalRing R) (_ : Algebra ℂ R),
      IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧
      ringKrullDim R = 3 ∧
      Function.Bijective (algebraMap ℂ (IsLocalRing.ResidueField R))
end SmallCM


end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.SmallCM.candidate_ring_properties_statement

end Problem

/- Formalization scope, from lean/docs/195.md: The small Cohen–Macaulay module conjecture asks whether every complete local domain has a nonzero finitely generated maximal Cohen–Macaulay module. The linked formalization verifies only the ring-theoretic candidate: there exists a three-dimensional complete Noetherian integrally closed local domain over $\mathbb C$ whose residue field is $\mathbb C$. It does not prove that this ring lacks a nonzero finitely generated maximal Cohen–Macaulay module, or the paper's counterexample essentially of finite type. -/
/- A supporting-result comparison, not the paper's main theorem (lean/ComparatorChallenges/README.md). -/
