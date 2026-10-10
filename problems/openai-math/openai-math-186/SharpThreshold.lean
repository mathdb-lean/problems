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

- problem_id: SharpThreshold
- collection: openai-math
- question_id: openai-math:186
- source: openai-math
- source_locator: lean/ComparatorChallenges/SharpThreshold.lean#OAI.Problem313.sharp_threshold_width
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves the Friedgut–Kalai threshold-width conjectures for graphs and fixed-uniformity hypergraphs. For fixed $`0\lt \varepsilon\lt 1/2`$, every nontrivial increasing relabeling-invariant property crosses from probability ε to $`1-\varepsilon`$ within width $`O((\log n)^{-2})`$ for graphs and $`O_r((\log n)^{-r/(r-1)})`$ for r-uniform hypergraphs, r ≥ 3. The hypergraph influence bound also applies to nonmonotone properties. ([Lean](lean/docs/186.md)) We prove the Friedgut–Kalai sharp-threshold conjecture. For every integer n ≥ 2, every nontrivial increasing family of graphs on n vertices invariant under all vertex permutations, and every $`0\lt \varepsilon\lt 1/2`$, the edge probabilities at which its probability equals ε and $`1-\varepsilon`$ differ by at most $`C\log(1/(2\varepsilon))/(\log n)^2`$, for a universal constant C.
- notes: OpenAI math result family 186, Uniform influence and sharp thresholds for graph and hypergraph properties -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/186.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Problem313.sharp_threshold_width
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.SharpThreshold.Main
- source_papers: preprints/A-Sharp-Threshold-Bound-for-Monotone-Graph-Properties-September-25-2026/paper.pdf
- source_scope_note: lean/docs/186.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

namespace Problem313

abbrev GraphEdge (n : ℕ) := {e : Finset (Fin n) // e.card = 2}

abbrev GraphConfig (n : ℕ) := GraphEdge n → Bool

def permEdge {n : ℕ} (π : Equiv.Perm (Fin n)) (e : GraphEdge n) : GraphEdge n :=
  ⟨e.1.map π.toEmbedding, by simpa using e.2⟩

def permuteConfig {n : ℕ} (π : Equiv.Perm (Fin n))
    (x : GraphConfig n) : GraphConfig n :=
  fun e => x (permEdge π.symm e)

def VertexInvariant {n : ℕ} (f : GraphConfig n → Bool) : Prop :=
  ∀ (π : Equiv.Perm (Fin n)) (x : GraphConfig n),
    f (permuteConfig π x) = f x

def ConfigLE {n : ℕ} (x y : GraphConfig n) : Prop :=
  ∀ e, x e = true → y e = true

def IncreasingGraphProperty {n : ℕ} (f : GraphConfig n → Bool) : Prop :=
  ∀ x y, ConfigLE x y → f x = true → f y = true

def NontrivialGraphProperty {n : ℕ} (f : GraphConfig n → Bool) : Prop :=
  (∃ x, f x = true) ∧ (∃ x, f x = false)

def boolReal (b : Bool) : ℝ :=
  match b with
  | false => 0
  | true => 1

def graphWeight {n : ℕ} (p : ℝ) (x : GraphConfig n) : ℝ := by
  classical
  exact Finset.univ.prod (fun e : GraphEdge n =>
    if x e = true then p else 1 - p)

def graphMean {n : ℕ} (p : ℝ) (f : GraphConfig n → Bool) : ℝ := by
  classical
  exact Finset.univ.sum (fun x : GraphConfig n =>
    graphWeight p x * boolReal (f x))

def graphQuantile {n : ℕ} (a : ℝ) (f : GraphConfig n → Bool) : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ graphMean p f ≥ a}

def sharp_threshold_width_statement : Prop :=
  ∀ (n : ℕ) (f : GraphConfig n → Bool) (ε : ℝ),
      2 ≤ n → VertexInvariant f → IncreasingGraphProperty f →
      NontrivialGraphProperty f → 0 < ε → ε < (1 / 2 : ℝ) →
      graphQuantile (1 - ε) f - graphQuantile ε f ≤
        ((2 : ℝ) ^ 19 / (Real.log (n : ℝ)) ^ 2) * Real.log (1 / (2 * ε))

end Problem313

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Problem313.sharp_threshold_width_statement

end Problem

/- Formalization scope, from lean/docs/186.md: The Friedgut–Kalai sharp-threshold conjecture concerns how quickly a nontrivial increasing graph property appears in the independent-edge random graph. For every $n\ge2$, every such property invariant under vertex relabeling, and $0<\varepsilon<1/2$, the formalization proves that the edge-probability interval between probabilities $\varepsilon$ and $1-\varepsilon$ has width at most $2^{19}\log(1/(2\varepsilon))/(\log n)^2$. The constant is uniform over the graph property, $n$, and $\varepsilon$. -/
