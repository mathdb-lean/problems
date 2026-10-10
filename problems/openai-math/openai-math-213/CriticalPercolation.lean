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

- problem_id: CriticalPercolation
- collection: openai-math
- question_id: openai-math:213
- source: openai-math
- source_locator: lean/ComparatorChallenges/CriticalPercolation.lean#OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves the Benjamini–Schramm criticality conjecture for bond percolation on every infinite connected locally finite quasi-transitive graph with $`p_c\lt 1`$: at the critical probability, there is almost surely no infinite cluster. The family also establishes this conclusion for both nearest-neighbor bond and site percolation on ℤ3. ([Lean](lean/docs/213.md)) We prove that nearest-neighbor Bernoulli bond and site percolation on ℤ3 have no infinite cluster at their respective critical parameters. The proof combines a finite connection inequality for independent hyperedges with a finite-scale extension estimate and an adaptive exploration. We prove that critical Bernoulli bond percolation has no infinite cluster on any infinite connected locally finite quasi-transitive graph with critical probability less than one. This resolves the bond form of the criticality conjecture of Benjamini and Schramm.
- notes: OpenAI math result family 213, Critical percolation on every quasi-transitive graph -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/213.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality
- source_theorem_count: 1
- source_solution_module: OAI.Probability.CriticalPercolation.Main
- source_papers: preprints/Critical-bond-and-site-percolation-on-the-cubic-lattice-September-24-2026/paper.pdf preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf
- source_scope_note: lean/docs/213.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

open Set MeasureTheory ProbabilityTheory

namespace CriticalPercolation

/-- An undirected graph with labelled bonds, including loops and parallel bonds. -/
structure BondGraph (V E : Type*) where
  ends : E → Sym2 V

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

/-- The graph of retained bonds. `fromEdgeSet` discards loops. -/
def openGraph (ω : Set E) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (G.ends '' ω)

/-- The underlying connectivity graph with every bond retained. -/
def fullGraph : SimpleGraph V := G.openGraph Set.univ

/-- Local finiteness counts bonds, not just distinct neighbors. -/
def LocallyFinite : Prop := ∀ v : V, {e : E | v ∈ G.ends e}.Finite

/-- Automorphisms preserve the vertex and bond structure, including multiplicities. -/
structure Aut where
  vertex : V ≃ V
  edge : E ≃ E
  preserves : ∀ e, G.ends (edge e) = Sym2.map vertex (G.ends e)

/-- Finitely many vertex orbits under the full automorphism group. -/
def QuasiTransitive : Prop :=
  ∃ S : Set V, S.Finite ∧ ∀ v : V, ∃ s ∈ S, ∃ φ : G.Aut, φ.vertex s = v

/-- Finite open paths, including the path of length zero, define the open cluster. -/
def cluster (ω : Set E) (v : V) : Set V := {w | (G.openGraph ω).Reachable v w}

/-- The event that at least one open cluster is infinite. -/
def percolates : Set (Set E) := {ω | ∃ v : V, (G.cluster ω v).Infinite}

/-- Independent retention with parameter `p ∈ [0,1]` of each labelled bond. -/
noncomputable def law (_G : BondGraph V E) (p : unitInterval) : Measure (Set E) :=
  ProbabilityTheory.setBernoulli Set.univ p

/-- The infimum of parameters with positive probability of an infinite cluster. -/
noncomputable def criticalProbability : unitInterval :=
  sInf {p : unitInterval | 0 < G.law p G.percolates}

/-- Critical Bernoulli bond percolation has no infinite cluster when the critical
probability is below one. -/
def no_percolation_at_criticality_statement : Prop :=
  ∀ {V E : Type*} (G : BondGraph V E) [Infinite V] (hconnected : G.fullGraph.Connected) (hlocal : G.LocallyFinite) (hquasi : G.QuasiTransitive) (hpc : G.criticalProbability < 1),
    G.law G.criticalProbability G.percolates = 0

end BondGraph
end CriticalPercolation

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u_1, u_2} : Prop :=
  _root_.OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality_statement.{u_1, u_2}

end Problem

/- Formalization scope, from lean/docs/213.md: The critical-percolation question asks whether an infinite cluster can remain at the threshold. The formalized result proves that, at their respective critical probabilities, nearest-neighbor bond and site percolation on $\mathbb Z^3$ almost surely have no infinite cluster. Equivalently, almost surely every vertex belongs to a finite cluster in each model. The formalization proves absence of an infinite cluster at criticality for Bernoulli bond percolation on every infinite connected locally finite quasi-transitive graph with critical probability $p_c<1$. At $p=p_c$, the probability that any infinite cluster exists is zero. The graph model permits bond multiplicities. -/
