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

- problem_id: SidorenkoCounterexample
- collection: openai-math
- question_id: openai-math:161
- source: openai-math
- source_locator: lean/ComparatorChallenges/SidorenkoCounterexample.lean#OAI.SidorenkoCounterexample.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Disproves Sidorenko's conjecture with a connected bipartite pattern on 35 vertices and 66 edges that occurs less frequently than in a random graph of the same edge density. The same pattern disproves the forcing conjecture of Skokan and Thoma: matching its density and the edge density of a constant graphon need not force quasirandomness. ([Lean](lean/docs/161.md)) We disprove Sidorenko's conjecture with a bipartite graph on 35 vertices and 66 edges: its homomorphism density in some finite simple graph is smaller than the conjectured lower bound. The same connected graph also disproves the forcing conjecture: at one fixed density, asymptotically matching the edge and pattern densities does not imply quasirandomness.
- notes: OpenAI math result family 161, Counterexamples to Sidorenko’s conjecture and the forcing conjecture -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/161.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.SidorenkoCounterexample.main
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.Sidorenko.RandomHost
- source_papers: preprints/A-counterexample-to-Sidorenkos-conjecture-September-23-2026/paper.pdf
- source_scope_note: lean/docs/161.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-! # A finite counterexample to Sidorenko's conjecture

The pattern is the incidence graph of the 22 triples in Table 1 of the source.
Homomorphism density counts all edge-preserving maps, including noninjective maps.
-/

namespace SidorenkoCounterexample

def faces : Fin 22 → Finset (Fin 13) := ![
  {0,1,3}, {0,1,9}, {0,2,3}, {0,2,9}, {1,3,10}, {1,7,10},
  {1,7,12}, {1,9,12}, {2,3,4}, {2,4,9}, {3,4,11}, {3,10,11},
  {4,8,9}, {4,8,11}, {5,6,7}, {5,6,11}, {5,7,10}, {5,10,11},
  {6,7,12}, {6,8,11}, {6,8,12}, {8,9,12}]

abbrev PatternVertex := Fin 13 ⊕ Fin 22

def incidence : PatternVertex → PatternVertex → Prop
  | .inl point, .inr face => point ∈ faces face
  | .inr face, .inl point => point ∈ faces face
  | _, _ => False

def H : SimpleGraph PatternVertex where
  Adj := incidence
  symm.symm := by intro left right; cases left <;> cases right <;> simp [incidence]
  loopless.irrefl := by intro vertex; cases vertex <;> simp [incidence]

noncomputable def homCount {V W : Type*} (F : SimpleGraph V) (G : SimpleGraph W) : ℕ :=
  Nat.card {hom : V → W // ∀ left right, F.Adj left right → G.Adj (hom left) (hom right)}

noncomputable def homDensity {V W : Type*} (F : SimpleGraph V) (G : SimpleGraph W) : ℝ :=
  (homCount F G : ℝ) / (Nat.card W : ℝ) ^ Nat.card V

noncomputable def edgeDensity {W : Type*} (G : SimpleGraph W) : ℝ :=
  2 * (Nat.card G.edgeSet : ℝ) / (Nat.card W : ℝ) ^ 2

/-- A finite simple host with at least one edge violates Sidorenko's inequality. -/
def main_statement : Prop :=
  ∃ size : ℕ, 0 < size ∧ ∃ host : SimpleGraph (Fin size),
    (∃ left right, host.Adj left right) ∧ homDensity H host < (edgeDensity host) ^ 66

end SidorenkoCounterexample

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.SidorenkoCounterexample.main_statement

end Problem

/- Formalization scope, from lean/docs/161.md: Sidorenko's conjecture predicts that every bipartite graph $H$ has homomorphism density at least the host graph's edge density raised to $|E(H)|$. The formalization disproves this for the paper's fixed bipartite graph with $35$ vertices and $66$ edges: it constructs a nonempty finite simple host graph with $t(H,G)<t(K_2,G)^{66}$. The separate forcing-conjecture consequence in the paper is outside this statement. -/
