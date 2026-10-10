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

- problem_id: HoneycombFreeEnergy
- collection: openai-math
- question_id: openai-math:237
- source: openai-math
- source_locator: lean/ComparatorChallenges/HoneycombFreeEnergy.lean#OAI.HoneycombForce.logPartition_tendsto
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves the diameter form of Nienhuis's predicted three-quarter exponent: a uniformly chosen n-step self-avoiding walk on the honeycomb lattice has diameter $`n^{3/4+o(1)}`$. Its local mass and covering numbers have exponent 4/3. These estimates hold at every sufficiently large fixed length, simultaneously across scales, with arbitrarily high polynomial probability. ([Lean](lean/docs/237.md)) We prove that, under the all-length critical measure, a honeycomb bridge crossing a strip of h layers, with its initial port fixed and its terminal port free, has mean length $`h^{4/3+o(1)}`$. We also obtain central visit probability $`R^{-2/3+o(1)}`$ and mean length $`R^{4/3+o(1)}`$ for macroscopic free-boundary chords in a regular hexagon. For critical honeycomb self-avoiding walk, we prove spatial exponent 3/4 for the infinite irreducible-bridge law and for bridges of every sufficiently large compatible even length. We establish the corresponding thermal laws at every large discount scale, including all positive length and spatial moments. For unrestricted uniform walks, the endpoint lower law holds on a common set of lengths of natural density one. We also determine the near-critical exponential correlation scale and small-force free-energy exponent, and prove spatial local lower bounds that permit conditioning on a prescribed terminal vertex. At the critical weight of the regular honeycomb lattice, the total weight of self-avoiding paths crossing a strip of height N is comparable to N−1/4. The first horizontal-displacement moment of return paths is comparable to N3/4. Critical self-avoiding walks between prescribed, macroscopically separated boundary ports of a regular honeycomb hexagon have length $`R^{4/3+o(1)}`$ in probability, where R is the scale of the hexagon. We prove the corresponding statements for half-plane arches, parallel cuts and nonparallel pure cuts. The half-plane law also has mean length $`R^{4/3+o(1)}`$. A separate strip argument gives endpoint mean laws on one density-one set of heights and in an aligned, critically weighted mixture of all even heights in a macroscopic interval.
- notes: OpenAI math result family 237, The three-quarter exponent for honeycomb self-avoiding walk -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/237.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.HoneycombForce.logPartition_tendsto
- source_theorem_count: 1
- source_solution_module: OAI.Probability.Honeycomb.FreeEnergy
- source_papers: preprints/Polynomial-vacuum-representations-and-bridge-mass-for-honeycomb-walks-September-26-2026/main.pdf preprints/Renewal-and-changes-of-law-for-critical-honeycomb-walks-September-26-2026/main.pdf preprints/Critical-strip-crossing-mass-on-the-honeycomb-lattice-September-26-2026/main.pdf preprints/Critical-honeycomb-chords-with-prescribed-boundary-endpoints-September-26-2026/main.pdf
- source_scope_note: lean/docs/237.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-! Existence of the fixed-length forced free energy of honeycomb walks. -/

noncomputable section
open scoped ENNReal Topology
open Filter

namespace HoneycombForce

structure Vertex where
  col : ℤ
  row : ℤ
  up : Bool
  deriving DecidableEq

def up (i j : ℤ) : Vertex := ⟨i, j, true⟩

def down (i j : ℤ) : Vertex := ⟨i, j, false⟩

def rowSpacing : ℝ := Real.sqrt 3 / 2

def position (v : Vertex) : ℂ :=
  if v.up then
    ⟨(v.col : ℝ) + (v.row : ℝ) / 2 + 1/2,
      rowSpacing * ((v.row : ℝ) + 1/3)⟩
  else
    ⟨(v.col : ℝ) + (v.row : ℝ) / 2 + 1,
      rowSpacing * ((v.row : ℝ) + 2/3)⟩

def rho : ℝ := (Real.sqrt (2 + Real.sqrt 2))⁻¹

def neighbors (v : Vertex) : Finset Vertex :=
  if v.up then
    {down v.col (v.row-1), down v.col v.row, down (v.col-1) v.row}
  else
    {up v.col (v.row+1), up v.col v.row, up (v.col+1) v.row}

def walkLists (o : Vertex) : ℕ → Finset (List Vertex)
  | 0 => {[o]}
  | n+1 => (neighbors o).biUnion (fun v => (walkLists v n).image (List.cons o))

def saws (o : Vertex) (n : ℕ) : Finset (List Vertex) :=
  (walkLists o n).filter List.Nodup

def endpoint (o : Vertex) (γ : List Vertex) : Vertex := γ.getLastD o

def displacement (o : Vertex) (γ : List Vertex) : ℂ :=
  position (endpoint o γ) - position o

def projection (e z : ℂ) : ℝ := (star e * z).re

def partition (o : Vertex) (e : ℂ) (s : ℝ) (n : ℕ) : ℝ :=
  ∑ γ ∈ saws o n, rho ^ n * Real.exp (s * projection e (displacement o γ))

def logPartition (o : Vertex) (e : ℂ) (s : ℝ) (n : ℕ) : ℝ :=
  Real.log (partition o e s n) / (n : ℝ)

def freeEnergy (o : Vertex) (e : ℂ) (s : ℝ) : ℝ :=
  Filter.limUnder atTop (logPartition o e s)

def logPartition_tendsto_statement : Prop :=
  ∀ (o : Vertex) (e : ℂ) (s : ℝ),
    Tendsto (logPartition o e s) atTop (𝓝 (freeEnergy o e s))

end HoneycombForce

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.HoneycombForce.logPartition_tendsto_statement

end Problem

/- Formalization scope, from lean/docs/237.md: The linked formalization establishes finiteness of the critical bridge measures used in the paper. For every strip height $h\ge1$, the total weight and first length moment of self-avoiding honeycomb bridges from a fixed initial port to a free terminal port are finite. The corresponding sums are also finite when the bridge is confined to the corridor of horizontal width $h(\log h)^2$, including the normalized first-moment sums. These are supporting summability statements. The paper's $h^{4/3+o(1)}$ mean-length law and its central-visit and hexagonal-chord exponents are outside them. The linked formalization proves existence of the infinite-length free energy for the critical honeycomb self-avoiding-walk partition function. For every starting vertex, force direction, and real force parameter, the logarithm of the length-$n$ partition function divided by $n$ converges to its stated free-energy limit. This selected result supplies the limiting free energy. It does not state the paper's small-force exponent, near-critical correlation scale, or the $3/4$ spatial and moment laws. For critical self-avoiding walks on the honeycomb lattice, the formalization proves that the total weight of paths crossing a strip of height $N$ is comparable to $N^{-1/4}$, while the first horizontal-displacement moment of return paths is comparable to $N^{3/4}$. It also proves finiteness of the strip sums, the exact arch–bridge balance identity, comparison of successive moment increments with bridge mass, and monotonicity of bridge mass. The comparison constants are uniform in the strip height. For the prescribed-boundary-endpoint companion, let $B_h$ be the total critical weight of strict bridges crossing a strip of integral height $h$, from one fixed bottom port to all compatible top ports, with $B_0=1$. The formalization proves $c(1+h)^{-1/4}\le B_h\le C(1+h)^{-1/4}$ for all $h\ge0$ and fixed positive constants $c,C$. This includes finiteness of the path sum. The prescribed-endpoint length law, arch and strip mean laws, and remaining moment and renewal conclusions are outside this supporting statement. -/
