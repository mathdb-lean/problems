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

- problem_id: HoneycombBridgeMassSupport
- collection: openai-math
- question_id: openai-math:237
- source: openai-math
- source_locator: lean/ComparatorChallenges/HoneycombBridgeMassSupport.lean#OAI.CriticalHoneycomb.finiteBridgeMassEstimate
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves the diameter form of Nienhuis's predicted three-quarter exponent: a uniformly chosen n-step self-avoiding walk on the honeycomb lattice has diameter $`n^{3/4+o(1)}`$. Its local mass and covering numbers have exponent 4/3. These estimates hold at every sufficiently large fixed length, simultaneously across scales, with arbitrarily high polynomial probability. ([Lean](lean/docs/237.md)) We prove that, under the all-length critical measure, a honeycomb bridge crossing a strip of h layers, with its initial port fixed and its terminal port free, has mean length $`h^{4/3+o(1)}`$. We also obtain central visit probability $`R^{-2/3+o(1)}`$ and mean length $`R^{4/3+o(1)}`$ for macroscopic free-boundary chords in a regular hexagon. For critical honeycomb self-avoiding walk, we prove spatial exponent 3/4 for the infinite irreducible-bridge law and for bridges of every sufficiently large compatible even length. We establish the corresponding thermal laws at every large discount scale, including all positive length and spatial moments. For unrestricted uniform walks, the endpoint lower law holds on a common set of lengths of natural density one. We also determine the near-critical exponential correlation scale and small-force free-energy exponent, and prove spatial local lower bounds that permit conditioning on a prescribed terminal vertex. At the critical weight of the regular honeycomb lattice, the total weight of self-avoiding paths crossing a strip of height N is comparable to N−1/4. The first horizontal-displacement moment of return paths is comparable to N3/4. Critical self-avoiding walks between prescribed, macroscopically separated boundary ports of a regular honeycomb hexagon have length $`R^{4/3+o(1)}`$ in probability, where R is the scale of the hexagon. We prove the corresponding statements for half-plane arches, parallel cuts and nonparallel pure cuts. The half-plane law also has mean length $`R^{4/3+o(1)}`$. A separate strip argument gives endpoint mean laws on one density-one set of heights and in an aligned, critically weighted mixture of all even heights in a macroscopic interval.
- notes: OpenAI math result family 237, The three-quarter exponent for honeycomb self-avoiding walk -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/237.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.CriticalHoneycomb.finiteBridgeMassEstimate
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.HoneycombChords.BridgeMass
- source_main_result: OAI.CriticalHoneycomb.finiteBridgeMassEstimate
- source_papers: preprints/Polynomial-vacuum-representations-and-bridge-mass-for-honeycomb-walks-September-26-2026/main.pdf preprints/Renewal-and-changes-of-law-for-critical-honeycomb-walks-September-26-2026/main.pdf preprints/Critical-strip-crossing-mass-on-the-honeycomb-lattice-September-26-2026/main.pdf preprints/Critical-honeycomb-chords-with-prescribed-boundary-endpoints-September-26-2026/main.pdf
- source_scope_note: lean/docs/237.md
- source_field: Combinatorics
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace CriticalHoneycomb
open scoped ENNReal

abbrev Center := ℤ × ℤ × Bool

def up (i j : ℤ) : Center := (i, j, true)
def down (i j : ℤ) : Center := (i, j, false)

/-- Adjacency across a full triangular edge. -/
def Adj (v w : Center) : Prop :=
  if v.2.2 then
    w.2.2 = false ∧ ((w.1 = v.1 ∧ w.2.1 = v.2.1) ∨
      (w.1 = v.1 ∧ w.2.1 = v.2.1 - 1) ∨
      (w.1 = v.1 - 1 ∧ w.2.1 = v.2.1))
  else
    w.2.2 = true ∧ ((w.1 = v.1 ∧ w.2.1 = v.2.1) ∨
      (w.1 = v.1 ∧ w.2.1 = v.2.1 + 1) ∨
      (w.1 = v.1 + 1 ∧ w.2.1 = v.2.1))

noncomputable def rowSpacing : ℝ := Real.sqrt 3 / 2

/-- The fixed Euclidean embedding in the unit triangular tiling. -/
noncomputable def centerPosition (v : Center) : ℝ × ℝ :=
  if v.2.2 then
    ((v.1 : ℝ) + (v.2.1 : ℝ) / 2 + 1 / 2,
      rowSpacing * ((v.2.1 : ℝ) + 1 / 3))
  else
    ((v.1 : ℝ) + (v.2.1 : ℝ) / 2 + 1,
      rowSpacing * ((v.2.1 : ℝ) + 2 / 3))

/-- A midpoint port, oriented into the triangle domain. -/
structure Port (D : Set Center) where
  inside : Center
  outside : Center
  adjacent : Adj inside outside
  inside_mem : inside ∈ D
  outside_not_mem : outside ∉ D

noncomputable def Port.position {D : Set Center} (p : Port D) : ℝ × ℝ :=
  ((centerPosition p.inside).1 / 2 + (centerPosition p.outside).1 / 2,
    (centerPosition p.inside).2 / 2 + (centerPosition p.outside).2 / 2)

/-- A simple center trace, with no premature boundary exit. -/
def IsTrace (D : Set Center) (p : List Center) : Prop :=
  p.Nodup ∧ p.IsChain Adj ∧ ∀ v ∈ p, v ∈ D

noncomputable def kappa : ℝ := (2 + Real.sqrt 2) ^ (-(1 : ℝ) / 2)

/-- Length counts centers; the port half-edges contribute no factors. -/
noncomputable def weight (p : List Center) : ℝ≥0∞ :=
  ENNReal.ofReal (kappa ^ p.length)

/-- The source's strip and tilt-compatible terminal support. -/
def strip (h : ℕ) : Set Center := {v | 0 ≤ v.2.1 ∧ v.2.1 < (h : ℤ)}
def StrictBridge (h : ℕ) :=
  {p : List Center // IsTrace (strip h) p ∧ p.head? = some (up 0 0) ∧
    ∃ i : ℤ, p.getLast? = some (down i ((h : ℤ) - 1))}
noncomputable def bridgeMass (h : ℕ) : ℝ≥0∞ :=
  if h = 0 then 1 else ∑' p : StrictBridge h, weight p.val

/-- Necessary estimate c:finite(1), inputs.tex:13, on the actual path sum. -/
def FiniteBridgeMassEstimate : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ h : ℕ,
    ENNReal.ofReal (c * (1 + (h : ℝ)) ^ (-(1 : ℝ) / 4)) ≤ bridgeMass h ∧
    bridgeMass h ≤ ENNReal.ofReal (C * (1 + (h : ℝ)) ^ (-(1 : ℝ) / 4))

/-- Trusted reference hole only; missing necessary main obligation. -/
def finiteBridgeMassEstimate_statement : Prop :=
  FiniteBridgeMassEstimate

end CriticalHoneycomb


end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.CriticalHoneycomb.finiteBridgeMassEstimate_statement

end Problem

/- Formalization scope, from lean/docs/237.md: The linked formalization establishes finiteness of the critical bridge measures used in the paper. For every strip height $h\ge1$, the total weight and first length moment of self-avoiding honeycomb bridges from a fixed initial port to a free terminal port are finite. The corresponding sums are also finite when the bridge is confined to the corridor of horizontal width $h(\log h)^2$, including the normalized first-moment sums. These are supporting summability statements. The paper's $h^{4/3+o(1)}$ mean-length law and its central-visit and hexagonal-chord exponents are outside them. The linked formalization proves existence of the infinite-length free energy for the critical honeycomb self-avoiding-walk partition function. For every starting vertex, force direction, and real force parameter, the logarithm of the length-$n$ partition function divided by $n$ converges to its stated free-energy limit. This selected result supplies the limiting free energy. It does not state the paper's small-force exponent, near-critical correlation scale, or the $3/4$ spatial and moment laws. For critical self-avoiding walks on the honeycomb lattice, the formalization proves that the total weight of paths crossing a strip of height $N$ is comparable to $N^{-1/4}$, while the first horizontal-displacement moment of return paths is comparable to $N^{3/4}$. It also proves finiteness of the strip sums, the exact arch–bridge balance identity, comparison of successive moment increments with bridge mass, and monotonicity of bridge mass. The comparison constants are uniform in the strip height. For the prescribed-boundary-endpoint companion, let $B_h$ be the total critical weight of strict bridges crossing a strip of integral height $h$, from one fixed bottom port to all compatible top ports, with $B_0=1$. The formalization proves $c(1+h)^{-1/4}\le B_h\le C(1+h)^{-1/4}$ for all $h\ge0$ and fixed positive constants $c,C$. This includes finiteness of the path sum. The prescribed-endpoint length law, arch and strip mean laws, and remaining moment and renewal conclusions are outside this supporting statement. -/
/- A supporting-result comparison, not the paper's main theorem (lean/ComparatorChallenges/README.md). -/
