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

- problem_id: IndependentSets
- collection: openai-math
- question_id: openai-math:106
- source: openai-math
- source_locator: lean/ComparatorChallenges/IndependentSets.lean#OAI.LargeIndependentSets.mainTheoremReal
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: It is NP-hard to color a three-colorable graph using any fixed number c ≥ 3 of colors. More strongly, for every fixed $`0\lt \delta\lt 1/3`$, a deterministic polynomial-time reduction from 3SAT produces simple unweighted graphs that are three-colorable in the satisfiable case and have no independent set of size $`\delta n`$ otherwise, where n is the number of vertices. ([Lean](lean/docs/106.md)) We prove that, for every fixed $`0\lt \delta\lt 1/3`$, it is NP-hard to distinguish three-colorable graphs from graphs in which every independent set has fewer than δ times the number of vertices. Consequently, for every fixed integer c ≥ 3, finding a proper c-coloring of a three-colorable graph is NP-hard.
- notes: OpenAI math result family 106, Hardness of coloring three-colorable graphs -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/106.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.LargeIndependentSets.mainTheoremReal
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.IndependentSets.Main
- source_main_result: OAI.LargeIndependentSets.mainTheoremReal
- source_papers: preprints/Hardness-of-finding-large-independent-sets-in-three-colorable-graphs-September-24-2026/Hardness-of-finding-large-independent-sets-in-three-colorable-graphs-September-24-2026.pdf
- source_scope_note: lean/docs/106.md
- source_field: Combinatorics
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace LargeIndependentSets

structure Literal where
  name : ℕ
  positive : Bool
  deriving DecidableEq

structure Formula where
  clauses : List (List Literal)
  width : ∀ C ∈ clauses, C.length ≤ 3

def Formula.Satisfiable (φ : Formula) : Prop :=
  ∃ assignment : ℕ → Bool, ∀ C ∈ φ.clauses,
    ∃ l ∈ C, assignment l.name = l.positive

/-- Binary framing: `true,b` for a payload bit and `false` as terminator. -/
def frame : List Bool → List Bool
  | [] => [false]
  | b :: bs => true :: b :: frame bs

def nameBits (n : ℕ) : List Bool := frame n.bits

def literalBits (l : Literal) : List Bool := l.positive :: nameBits l.name

def clauseBits (C : List Literal) : List Bool :=
  nameBits C.length ++ C.flatMap literalBits

def formulaBits (φ : Formula) : List Bool :=
  nameBits φ.clauses.length ++ φ.clauses.flatMap clauseBits

/-- A nonempty, finite, simple, undirected, unweighted graph. -/
structure Graph where
  vertices : ℕ
  nonempty : 0 < vertices
  adj : Fin vertices → Fin vertices → Bool
  symm : ∀ u v, adj u v = adj v u
  loopless : ∀ u, adj u u = false

def Graph.Independent (G : Graph) (S : Finset (Fin G.vertices)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.adj u v = false

instance (G : Graph) (S : Finset (Fin G.vertices)) : Decidable (G.Independent S) :=
  inferInstanceAs (Decidable (∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.adj u v = false))

def Graph.independenceNumber (G : Graph) : ℕ :=
  ((Finset.univ : Finset (Fin G.vertices)).powerset.filter G.Independent).sup Finset.card

def Graph.ThreeColorable (G : Graph) : Prop :=
  ∃ color : Fin G.vertices → Fin 3,
    ∀ u v, G.adj u v = true → color u ≠ color v

/-- Full explicit adjacency matrix, row-major, with binary vertex count. -/
def graphBits (G : Graph) : List Bool :=
  nameBits G.vertices ++ (List.finRange G.vertices).flatMap
    (fun u => (List.finRange G.vertices).map (G.adj u))

open scoped Classical
noncomputable section

/-- Polynomial-time graph reduction with a real independence-ratio threshold. -/
structure RealGraphReduction (δ : ℝ) where
  reduce : List Bool → Graph
  computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) graphBits reduce
  finiteAlphabets : ∀ k : computation.tm.K, Finite (computation.tm.Γ k)
  outputBound : Polynomial ℕ
  outputSize : ∀ b, (graphBits (reduce b)).length ≤ outputBound.eval b.length
  completeness : ∀ φ : Formula, φ.Satisfiable → (reduce (formulaBits φ)).ThreeColorable
  soundness : ∀ φ : Formula, ¬φ.Satisfiable →
    ((reduce (formulaBits φ)).independenceNumber : ℝ) <
      δ * (reduce (formulaBits φ)).vertices

/-- Real-threshold graph reduction with explicit binary runtime and output-size bounds. -/
def mainTheoremReal_statement : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 / 3 → Nonempty (RealGraphReduction δ)

end
end LargeIndependentSets

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.LargeIndependentSets.mainTheoremReal_statement

end Problem

/- Formalization scope, from lean/docs/106.md: The formalized result shows hardness of finding large independent sets even under a three-colorability promise. For every fixed $0<\delta<1/3$, a deterministic polynomial-time reduction maps binary 3SAT formulas to nonempty finite simple graphs. Satisfiable formulas produce three-colorable graphs; unsatisfiable formulas produce graphs whose largest independent set has fewer than $\delta$ times the number of vertices. The complete adjacency-matrix output is included in the runtime bound. -/
