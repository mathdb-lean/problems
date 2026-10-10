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

- problem_id: HoneycombBridgeFiniteness
- collection: openai-math
- question_id: openai-math:237
- source: openai-math
- source_locator: lean/ComparatorChallenges/HoneycombBridgeFiniteness.lean#OAI.PolynomialVacuumBridge.Corridor.finite_bridge_sums
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves the diameter form of Nienhuis's predicted three-quarter exponent: a uniformly chosen n-step self-avoiding walk on the honeycomb lattice has diameter $`n^{3/4+o(1)}`$. Its local mass and covering numbers have exponent 4/3. These estimates hold at every sufficiently large fixed length, simultaneously across scales, with arbitrarily high polynomial probability. ([Lean](lean/docs/237.md)) We prove that, under the all-length critical measure, a honeycomb bridge crossing a strip of h layers, with its initial port fixed and its terminal port free, has mean length $`h^{4/3+o(1)}`$. We also obtain central visit probability $`R^{-2/3+o(1)}`$ and mean length $`R^{4/3+o(1)}`$ for macroscopic free-boundary chords in a regular hexagon. For critical honeycomb self-avoiding walk, we prove spatial exponent 3/4 for the infinite irreducible-bridge law and for bridges of every sufficiently large compatible even length. We establish the corresponding thermal laws at every large discount scale, including all positive length and spatial moments. For unrestricted uniform walks, the endpoint lower law holds on a common set of lengths of natural density one. We also determine the near-critical exponential correlation scale and small-force free-energy exponent, and prove spatial local lower bounds that permit conditioning on a prescribed terminal vertex. At the critical weight of the regular honeycomb lattice, the total weight of self-avoiding paths crossing a strip of height N is comparable to N−1/4. The first horizontal-displacement moment of return paths is comparable to N3/4. Critical self-avoiding walks between prescribed, macroscopically separated boundary ports of a regular honeycomb hexagon have length $`R^{4/3+o(1)}`$ in probability, where R is the scale of the hexagon. We prove the corresponding statements for half-plane arches, parallel cuts and nonparallel pure cuts. The half-plane law also has mean length $`R^{4/3+o(1)}`$. A separate strip argument gives endpoint mean laws on one density-one set of heights and in an aligned, critically weighted mixture of all even heights in a macroscopic interval.
- notes: OpenAI math result family 237, The three-quarter exponent for honeycomb self-avoiding walk -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/237.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.PolynomialVacuumBridge.Corridor.finite_bridge_sums
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.HoneycombCorridor.BridgeFiniteness
- source_papers: preprints/Polynomial-vacuum-representations-and-bridge-mass-for-honeycomb-walks-September-26-2026/main.pdf preprints/Renewal-and-changes-of-law-for-critical-honeycomb-walks-September-26-2026/main.pdf preprints/Critical-strip-crossing-mass-on-the-honeycomb-lattice-September-26-2026/main.pdf preprints/Critical-honeycomb-chords-with-prescribed-boundary-endpoints-September-26-2026/main.pdf
- source_scope_note: lean/docs/237.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace PolynomialVacuumBridge.Corridor

inductive Vertex where
  | up (i j : ℤ)
  | down (i j : ℤ)
  deriving DecidableEq

noncomputable def position : Vertex → ℝ × ℝ
  | .up i j => ((i : ℝ) + (j : ℝ) / 2,
      ((j : ℝ) + 1 / 3) * (Real.sqrt 3 / 2))
  | .down i j => ((i : ℝ) + (j : ℝ) / 2 + 1 / 2,
      ((j : ℝ) + 2 / 3) * (Real.sqrt 3 / 2))

def adjacent : Vertex → Vertex → Prop
  | .up i j, .down k l =>
      (k = i ∧ l = j - 1) ∨ (k = i ∧ l = j) ∨ (k = i - 1 ∧ l = j)
  | .down k l, .up i j =>
      (k = i ∧ l = j - 1) ∨ (k = i ∧ l = j) ∨ (k = i - 1 ∧ l = j)
  | _, _ => False

noncomputable def criticalActivity : ℝ := (2 * Real.cos (Real.pi / 8))⁻¹
noncomputable def layer (vertex : Vertex) : ℤ :=
  Vertex.rec (fun _ vertical => vertical) (fun _ vertical => vertical) vertex

structure BridgePath (h : ℕ) where
  vertices : List Vertex
  distinct : vertices.Nodup
  connected : vertices.IsChain adjacent
  source : vertices.head? = some (.up 0 0)
  terminal : ∃ i : ℤ, vertices.getLast? = some (.down i ((h : ℤ) - 1))
  inStrip : ∀ v ∈ vertices, 0 ≤ layer v ∧ layer v < (h : ℤ)

noncomputable def weight {h : ℕ} (p : BridgePath h) : ℝ :=
  criticalActivity ^ p.vertices.length

noncomputable def firstLengthWeight {h : ℕ} (p : BridgePath h) : ℝ :=
  (p.vertices.length : ℝ) * weight p

noncomputable def bridgeMass (h : ℕ) : ℝ := ∑' p : BridgePath h, weight p
noncomputable def InLogCorridor {h : ℕ} (p : BridgePath h) : Prop :=
  ∀ v ∈ p.vertices, |(position v).1| ≤ (h : ℝ) * (Real.log (h : ℝ)) ^ 2

def ConfinedBridgePath (h : ℕ) := {p : BridgePath h // InLogCorridor p}

noncomputable def confinedMass (h : ℕ) : ℝ :=
  ∑' p : ConfinedBridgePath h, weight p.val
def FiniteBridgeSums : Prop :=
  ∀ h : ℕ, 1 ≤ h →
    Summable (weight (h := h)) ∧ Summable (firstLengthWeight (h := h)) ∧
    Summable (fun p : BridgePath h => firstLengthWeight p / bridgeMass h) ∧
    Summable (fun p : ConfinedBridgePath h => weight p.val) ∧
    Summable (fun p : ConfinedBridgePath h => firstLengthWeight p.val) ∧
    Summable (fun p : ConfinedBridgePath h => firstLengthWeight p.val / confinedMass h)


def finite_bridge_sums_statement : Prop :=
  FiniteBridgeSums

end PolynomialVacuumBridge.Corridor

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.PolynomialVacuumBridge.Corridor.finite_bridge_sums_statement

end Problem

/- Formalization scope, from lean/docs/237.md: The linked formalization establishes finiteness of the critical bridge measures used in the paper. For every strip height $h\ge1$, the total weight and first length moment of self-avoiding honeycomb bridges from a fixed initial port to a free terminal port are finite. The corresponding sums are also finite when the bridge is confined to the corridor of horizontal width $h(\log h)^2$, including the normalized first-moment sums. These are supporting summability statements. The paper's $h^{4/3+o(1)}$ mean-length law and its central-visit and hexagonal-chord exponents are outside them. The linked formalization proves existence of the infinite-length free energy for the critical honeycomb self-avoiding-walk partition function. For every starting vertex, force direction, and real force parameter, the logarithm of the length-$n$ partition function divided by $n$ converges to its stated free-energy limit. This selected result supplies the limiting free energy. It does not state the paper's small-force exponent, near-critical correlation scale, or the $3/4$ spatial and moment laws. For critical self-avoiding walks on the honeycomb lattice, the formalization proves that the total weight of paths crossing a strip of height $N$ is comparable to $N^{-1/4}$, while the first horizontal-displacement moment of return paths is comparable to $N^{3/4}$. It also proves finiteness of the strip sums, the exact arch–bridge balance identity, comparison of successive moment increments with bridge mass, and monotonicity of bridge mass. The comparison constants are uniform in the strip height. For the prescribed-boundary-endpoint companion, let $B_h$ be the total critical weight of strict bridges crossing a strip of integral height $h$, from one fixed bottom port to all compatible top ports, with $B_0=1$. The formalization proves $c(1+h)^{-1/4}\le B_h\le C(1+h)^{-1/4}$ for all $h\ge0$ and fixed positive constants $c,C$. This includes finiteness of the path sum. The prescribed-endpoint length law, arch and strip mean laws, and remaining moment and renewal conclusions are outside this supporting statement. -/
