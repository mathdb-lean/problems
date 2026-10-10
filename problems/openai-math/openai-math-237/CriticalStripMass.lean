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

- problem_id: CriticalStripMass
- collection: openai-math
- question_id: openai-math:237
- source: openai-math
- source_locator: lean/ComparatorChallenges/CriticalStripMass.lean#OAI.CriticalStrip.critical_strip_mass
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves the diameter form of Nienhuis's predicted three-quarter exponent: a uniformly chosen n-step self-avoiding walk on the honeycomb lattice has diameter $`n^{3/4+o(1)}`$. Its local mass and covering numbers have exponent 4/3. These estimates hold at every sufficiently large fixed length, simultaneously across scales, with arbitrarily high polynomial probability. ([Lean](lean/docs/237.md)) We prove that, under the all-length critical measure, a honeycomb bridge crossing a strip of h layers, with its initial port fixed and its terminal port free, has mean length $`h^{4/3+o(1)}`$. We also obtain central visit probability $`R^{-2/3+o(1)}`$ and mean length $`R^{4/3+o(1)}`$ for macroscopic free-boundary chords in a regular hexagon. For critical honeycomb self-avoiding walk, we prove spatial exponent 3/4 for the infinite irreducible-bridge law and for bridges of every sufficiently large compatible even length. We establish the corresponding thermal laws at every large discount scale, including all positive length and spatial moments. For unrestricted uniform walks, the endpoint lower law holds on a common set of lengths of natural density one. We also determine the near-critical exponential correlation scale and small-force free-energy exponent, and prove spatial local lower bounds that permit conditioning on a prescribed terminal vertex. At the critical weight of the regular honeycomb lattice, the total weight of self-avoiding paths crossing a strip of height N is comparable to N−1/4. The first horizontal-displacement moment of return paths is comparable to N3/4. Critical self-avoiding walks between prescribed, macroscopically separated boundary ports of a regular honeycomb hexagon have length $`R^{4/3+o(1)}`$ in probability, where R is the scale of the hexagon. We prove the corresponding statements for half-plane arches, parallel cuts and nonparallel pure cuts. The half-plane law also has mean length $`R^{4/3+o(1)}`$. A separate strip argument gives endpoint mean laws on one density-one set of heights and in an aligned, critically weighted mixture of all even heights in a macroscopic interval.
- notes: OpenAI math result family 237, The three-quarter exponent for honeycomb self-avoiding walk -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/237.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.CriticalStrip.critical_strip_mass
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.StripMass.Main
- source_papers: preprints/Polynomial-vacuum-representations-and-bridge-mass-for-honeycomb-walks-September-26-2026/main.pdf preprints/Renewal-and-changes-of-law-for-critical-honeycomb-walks-September-26-2026/main.pdf preprints/Critical-strip-crossing-mass-on-the-honeycomb-lattice-September-26-2026/main.pdf preprints/Critical-honeycomb-chords-with-prescribed-boundary-endpoints-September-26-2026/main.pdf
- source_scope_note: lean/docs/237.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

 

namespace CriticalStrip

noncomputable section
open scoped BigOperators
open Set MeasureTheory

def rho : ℝ := 1 / Real.sqrt (2 + Real.sqrt 2)
def c : ℝ := Real.cos (3 * Real.pi / 8)
def lambda : ℝ := Real.pi / 8
def d : ℝ := Real.cos (2 * lambda)
def C : ℝ := Real.cos lambda
def eta : ℝ := 2 * d - 1

abbrev Triangle := ℤ × ℕ × Bool

def up (i : ℤ) (j : ℕ) : Triangle := (i, j, true)
def down (i : ℤ) (j : ℕ) : Triangle := (i, j, false)

def upDownAdjacent (v w : Triangle) : Prop :=
  v.2.2 = true ∧ w.2.2 = false ∧
    ((v.2.1 = w.2.1 ∧ (w.1 = v.1 ∨ w.1 + 1 = v.1)) ∨
      (v.2.1 = w.2.1 + 1 ∧ v.1 = w.1))

def adjacent (v w : Triangle) : Prop := upDownAdjacent v w ∨ upDownAdjacent w v

 
def IsPath (N : ℕ) (finish : Triangle) (p : List Triangle) : Prop :=
  p.head? = some (up 0 0) ∧ p.getLast? = some finish ∧ p.Nodup ∧
  p.IsChain adjacent ∧ ∀ v ∈ p, v.2.1 < N

 
def archWeight (N : ℕ) (k : ℤ) (p : List Triangle) : ℝ := by
  classical
  exact if k ≠ 0 ∧ IsPath N (up k 0) p then rho ^ p.length else 0

 
def bridgeWeight (N : ℕ) (k : ℤ) (p : List Triangle) : ℝ := by
  classical
  exact if 0 < N ∧ IsPath N (down k (N - 1)) p then rho ^ p.length else 0

def K (N : ℕ) (k : ℤ) : ℝ := ∑' p, archWeight N k p
def bridgeKernel (N : ℕ) (k : ℤ) : ℝ := ∑' p, bridgeWeight N k p
def archMass (N : ℕ) : ℝ := ∑' k : ℤ, K N k
def bridgeMass (N : ℕ) : ℝ := ∑' k : ℤ, bridgeKernel N k
def moment (N : ℕ) : ℝ := ∑' k : ℕ, (k + 1 : ℝ) * K N (k + 1)

 
def StripSumsFinite (N : ℕ) : Prop :=
  (∀ k : ℤ, Summable (archWeight N k)) ∧
  (∀ k : ℤ, Summable (bridgeWeight N k)) ∧
  Summable (K N) ∧ Summable (bridgeKernel N) ∧
  Summable (fun k : ℕ => (k + 1 : ℝ) * K N (k + 1))

 
def Comparable (f g : ℕ → ℝ) : Prop :=
  ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧
    ∀ N : ℕ, 1 ≤ N → lo * g N ≤ f N ∧ f N ≤ hi * g N

 
def CriticalStripMass : Prop :=
  (∀ N : ℕ, 1 ≤ N → StripSumsFinite N) ∧
  (∀ N : ℕ, 1 ≤ N → c * archMass N + bridgeMass N = 1) ∧
  Comparable (fun N => moment (N + 1) - moment N) bridgeMass ∧
  Comparable moment (fun N => (N : ℝ) ^ (3 / 4 : ℝ)) ∧
  Comparable bridgeMass (fun N => (N : ℝ) ^ (-(1 / 4) : ℝ)) ∧
  (∀ N : ℕ, 1 ≤ N → bridgeMass (N + 1) ≤ bridgeMass N)

 

def critical_strip_mass_statement : Prop :=
  CriticalStripMass

end
end CriticalStrip

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.CriticalStrip.critical_strip_mass_statement

end Problem

/- Formalization scope, from lean/docs/237.md: The linked formalization establishes finiteness of the critical bridge measures used in the paper. For every strip height $h\ge1$, the total weight and first length moment of self-avoiding honeycomb bridges from a fixed initial port to a free terminal port are finite. The corresponding sums are also finite when the bridge is confined to the corridor of horizontal width $h(\log h)^2$, including the normalized first-moment sums. These are supporting summability statements. The paper's $h^{4/3+o(1)}$ mean-length law and its central-visit and hexagonal-chord exponents are outside them. The linked formalization proves existence of the infinite-length free energy for the critical honeycomb self-avoiding-walk partition function. For every starting vertex, force direction, and real force parameter, the logarithm of the length-$n$ partition function divided by $n$ converges to its stated free-energy limit. This selected result supplies the limiting free energy. It does not state the paper's small-force exponent, near-critical correlation scale, or the $3/4$ spatial and moment laws. For critical self-avoiding walks on the honeycomb lattice, the formalization proves that the total weight of paths crossing a strip of height $N$ is comparable to $N^{-1/4}$, while the first horizontal-displacement moment of return paths is comparable to $N^{3/4}$. It also proves finiteness of the strip sums, the exact arch–bridge balance identity, comparison of successive moment increments with bridge mass, and monotonicity of bridge mass. The comparison constants are uniform in the strip height. For the prescribed-boundary-endpoint companion, let $B_h$ be the total critical weight of strict bridges crossing a strip of integral height $h$, from one fixed bottom port to all compatible top ports, with $B_0=1$. The formalization proves $c(1+h)^{-1/4}\le B_h\le C(1+h)^{-1/4}$ for all $h\ge0$ and fixed positive constants $c,C$. This includes finiteness of the path sum. The prescribed-endpoint length law, arch and strip mean laws, and remaining moment and renewal conclusions are outside this supporting statement. -/
