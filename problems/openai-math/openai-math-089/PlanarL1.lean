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

- problem_id: PlanarL1
- collection: openai-math
- question_id: openai-math:089
- source: openai-math
- source_locator: lean/ComparatorChallenges/PlanarL1.lean#OAI.PlanarL1.planar_graph_metrics_embed_L1
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves the planar and bounded-treewidth cases of the Gupta–Newman–Rabinovich–Sinclair conjecture. Shortest-path metrics of finite connected graphs with arbitrary positive edge lengths embed into real L1 with universal distortion for planar graphs, and distortion depending only on treewidth for bounded-treewidth graphs. The corresponding multicommodity flow–cut gaps are uniformly bounded. ([Lean](lean/docs/089.md)) We prove that every finite connected planar graph with arbitrary positive real edge lengths embeds into real L1 with a universal distortion bound. This resolves the planar embedding conjecture positively. For every fixed treewidth bound, the shortest-path metrics of finite connected graphs with arbitrary positive real edge lengths embed into real L1 with uniformly bounded distortion. This resolves the bounded-treewidth case of the Gupta–Newman–Rabinovich–Sinclair conjecture positively.
- notes: OpenAI math result family 089, Bounded-distortion <i>L</i><sub>1</sub> embeddings of planar and bounded-treewidth graphs -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/089.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.PlanarL1.planar_graph_metrics_embed_L1
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.PlanarL1.Embedding
- source_main_result: OAI.PlanarL1.planar_graph_metrics_embed_L1
- source_papers: preprints/Planar-Graph-Metrics-Embed-into-L1-with-Constant-Distortion-September-23-2026/paper.pdf preprints/L1-Embeddings-of-Graphs-of-Bounded-Treewidth-September-23-2026/paper.pdf
- source_scope_note: lean/docs/089.md
- source_field: Combinatorics
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace PlanarL1

/-- A topological drawing by simple plane arcs, with injective vertex placement,
no vertex in an edge interior, and disjoint interiors for distinct unoriented edges. -/
def IsPlanar {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ (point : V → ℝ × ℝ) (arc : ∀ u v : V, G.Adj u v → C(unitInterval, ℝ × ℝ)),
    Function.Injective point ∧
    (∀ u v h, (arc u v h) 0 = point u ∧ (arc u v h) 1 = point v) ∧
    (∀ u v h, Function.Injective (arc u v h)) ∧
    (∀ u v h (t : unitInterval) w, 0 < (t : ℝ) → (t : ℝ) < 1 →
      (arc u v h) t ≠ point w) ∧
    (∀ u v h x y k (s t : unitInterval),
      0 < (s : ℝ) → (s : ℝ) < 1 → 0 < (t : ℝ) → (t : ℝ) < 1 →
      (arc u v h) s = (arc x y k) t →
      (u = x ∧ v = y) ∨ (u = y ∧ v = x))

/-- The sum of edge lengths along a finite graph walk. -/
def walkLength {V : Type} {G : SimpleGraph V} (length : V → V → ℝ)
    {u v : V} : G.Walk u v → ℝ
  | .nil => 0
  | @SimpleGraph.Walk.cons _ _ u w _ _ p => length u w + walkLength length p

/-- The infimum of lengths of actual walks between the two vertices. -/
noncomputable def graphDistance {V : Type} (G : SimpleGraph V)
    (length : V → V → ℝ) (u v : V) : ℝ :=
  sInf (Set.range (fun p : G.Walk u v => walkLength length p))

/-- One universal distortion bound for finite connected planar graphs with
arbitrary symmetric positive edge lengths, realized in a real `L¹` space. -/
def MainStatement : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (length : Fin n → Fin n → ℝ),
      G.Connected → IsPlanar G →
      (∀ u v, length u v = length v u) →
      (∀ u v, G.Adj u v → 0 < length u v) →
      ∃ (Ω : Type) (measurable : MeasurableSpace Ω)
          (μ : @MeasureTheory.Measure Ω measurable)
          (f : Fin n → @MeasureTheory.Lp Ω ℝ measurable _ 1 μ),
        ∀ x y, graphDistance G length x y ≤ ‖f x - f y‖ ∧
          ‖f x - f y‖ ≤ C * graphDistance G length x y

def planar_graph_metrics_embed_L1_statement : Prop :=
  MainStatement

end PlanarL1

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.PlanarL1.planar_graph_metrics_embed_L1_statement

end Problem

/- Formalization scope, from lean/docs/089.md: The planar case of the Gupta–Newman–Rabinovich–Sinclair embedding problem asks for a universal distortion bound in $L_1$. The formalized result gives one constant $C$ for every finite connected planar graph with arbitrary positive real edge lengths: its weighted shortest-path metric embeds into real $L_1$ with distortion at most $C$. The constant is independent of the number of vertices and the ratios between edge lengths; singleton graphs are included. The formalized result gives a uniform $L_1$ embedding bound for each bounded-treewidth class. For every bag-size bound $k\ge2$, there is a constant $C(k)$ such that the weighted shortest-path metric of every nonempty finite connected graph with a tree decomposition of bag size at most $k$ embeds into finite-dimensional real $L_1$ with distortion at most $C(k)$. Edge lengths may be arbitrary positive real numbers, and the constant is independent of the graph and decomposition size. -/
