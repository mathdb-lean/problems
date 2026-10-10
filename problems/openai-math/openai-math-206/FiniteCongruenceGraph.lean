import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Setoid.Basic
import Mathlib.Order.Hom.Basic
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

- problem_id: FiniteCongruenceGraph
- collection: openai-math
- question_id: openai-math:206
- source: openai-math
- source_locator: lean/ComparatorChallenges/FiniteCongruenceGraph.lean#OAI.FiniteCongruence.graph_criterion
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Some finite lattices are not congruence lattices of any finite algebra, answering the finite lattice representation problem negatively. Moreover, no algorithm decides whether a finite lattice has such a representation, or whether it is a full subgroup interval of a finite group. ([Lean](lean/docs/206.md)) We give an explicit colored-graph characterization of the finite nonempty lattices that occur as full congruence lattices of finite algebras, and prove that deciding this representation property is undecidable. In particular, the finite lattice representation problem has a negative answer. We also prove that recognition of full subgroup intervals in finite groups is undecidable.
- notes: OpenAI math result family 206, Finite lattice representation and undecidability -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/206.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.FiniteCongruence.graph_criterion
- source_theorem_count: 1
- source_solution_module: OAI.Algebra.Universal.GraphCriterion
- source_papers: preprints/Finite-Congruence-Lattices-Characterization-and-Undecidability-September-24-2026/paper.pdf
- source_scope_note: lean/docs/206.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace FiniteCongruence

structure Algebra (Carrier : Type) where
  numOps : ℕ
  arity : Fin numOps → ℕ
  op : (index : Fin numOps) → (Fin (arity index) → Carrier) → Carrier

def Compatible {Carrier : Type} (alg : Algebra Carrier) (rel : Setoid Carrier) : Prop :=
  ∀ (index : Fin alg.numOps) (left right : Fin (alg.arity index) → Carrier),
    (∀ coord, rel (left coord) (right coord)) → rel (alg.op index left) (alg.op index right)

def Congruence {Carrier : Type} (alg : Algebra Carrier) :=
  {rel : Setoid Carrier // Compatible alg rel}

instance {Carrier : Type} (alg : Algebra Carrier) : PartialOrder (Congruence alg) :=
  inferInstanceAs (PartialOrder {rel : Setoid Carrier // Compatible alg rel})

def Representable (Lat : Type) [PartialOrder Lat] : Prop :=
  ∃ size : ℕ, 0 < size ∧ ∃ alg : Algebra (Fin size), Nonempty (Lat ≃o Congruence alg)

def Admissible {Lat Carrier : Type} [LE Lat] (color : Carrier → Carrier → Lat)
    (placement : Carrier → Carrier) : Prop :=
  ∀ left right, color (placement left) (placement right) ≤ color left right

def Marked {Lat Carrier : Type} [LE Lat] (color : Carrier → Carrier → Lat)
    (seeds : Finset (Carrier × Carrier)) (left right : Carrier) : Prop :=
  ∃ placement : Carrier → Carrier, Admissible color placement ∧
    ∃ edge ∈ seeds, placement edge.1 = left ∧ placement edge.2 = right

def Connected {Lat Carrier : Type} [LE Lat] (color : Carrier → Carrier → Lat)
    (seeds : Finset (Carrier × Carrier)) (left right : Carrier) : Prop :=
  Relation.EqvGen (Marked color seeds) left right

def IsGraphWitness {Lat Carrier : Type} [Lattice Lat] [OrderBot Lat]
    (color : Carrier → Carrier → Lat) : Prop :=
  (∀ left right, color left right = color right left) ∧
  (∀ left right, color left right = ⊥ ↔ left = right) ∧
  (∀ left right middle, color left right ≤ color left middle ⊔ color middle right) ∧
  (∀ lower upper : Lat, ¬ lower ≤ upper →
    ∃ left right, color left right ≤ lower ∧ ¬ color left right ≤ upper) ∧
  (∀ seeds : Finset (Carrier × Carrier), seeds.Nonempty → ∀ left right,
    color left right ≤ seeds.sup (fun edge => color edge.1 edge.2) →
      Connected color seeds left right)

def HasGraphWitness (Lat : Type) [Lattice Lat] [OrderBot Lat] : Prop :=
  ∃ size : ℕ, 0 < size ∧ ∃ color : Fin size → Fin size → Lat, IsGraphWitness color

/-- A finite lattice is representable as the full congruence lattice of a nonempty finite
algebra exactly when it has a finite nonempty colored-graph witness. -/
def graph_criterion_statement : Prop :=
  ∀ (Lat : Type) [Fintype Lat] [Lattice Lat] [OrderBot Lat],
    Representable Lat ↔ HasGraphWitness Lat

end FiniteCongruence

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.FiniteCongruence.graph_criterion_statement

end Problem

/- Formalization scope, from lean/docs/206.md: The finite lattice representation problem asks which finite lattices occur as the full congruence lattice of a finite algebra. The formalization proves the paper's colored-graph characterization: a finite nonempty lattice is representable exactly when it admits the specified finite nonempty graph witness, whose edge colors encode the required congruence relations. This selected theorem is the equivalence with the graph criterion; the paper's undecidability and subgroup-interval conclusions are outside it. -/
