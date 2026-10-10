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

- problem_id: TriangleRemoval
- collection: openai-math
- question_id: openai-math:188
- source: openai-math
- source_locator: lean/ComparatorChallenges/TriangleRemoval.lean#OAI.SharpTerminalLeave.sharp_terminal_leave
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Starting from the complete graph on n vertices, repeatedly delete a uniformly chosen remaining triangle. The terminal edge count is asymptotic to $`n^{3/2}/(2\sqrt2)`$, with mean-square convergence after normalization by n3/2. This proves the triangle case of the Joos–Kühn sharp-constant conjecture. ([Lean](lean/docs/188.md)) Starting from the complete graph on n vertices, repeatedly remove the three edges of a uniformly chosen remaining triangle. We prove that the number of edges left at termination, divided by n3/2, converges in L2 to $`1/(2\sqrt2)`$. This proves the triangle case of the sharp-constant conjecture of Joos and Kühn. In particular, the same limit holds in probability and for the normalized expectation.
- notes: OpenAI math result family 188, The sharp terminal leave in random triangle removal -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/188.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.SharpTerminalLeave.sharp_terminal_leave
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.TriangleRemoval.Main
- source_papers: preprints/The-Sharp-Terminal-Leave-in-Random-Triangle-Removal-September-25-2026/The-Sharp-Terminal-Leave-in-Random-Triangle-Removal-September-25-2026.pdf
- source_scope_note: lean/docs/188.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

section
section

open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

abbrev Graph (n : ℕ) := Finset (Finset (Fin n))

def completeGraph (n : ℕ) : Graph n := Finset.univ.powersetCard 2

def triangles {n : ℕ} (G : Graph n) : Finset (Finset (Fin n)) :=
  (Finset.univ.powersetCard 3).filter (fun t => t.powersetCard 2 ⊆ G)

noncomputable def step {n : ℕ} (G : Graph n) : PMF (Graph n) :=
  if h : (triangles G).Nonempty then
    (PMF.uniformOfFinset (triangles G) h).map (fun t => G \ t.powersetCard 2)
  else PMF.pure G

noncomputable def evolve {n : ℕ} (G : Graph n) : ℕ → PMF (Graph n)
  | 0 => PMF.pure G
  | k + 1 => (evolve G k).bind step

noncomputable def terminalLaw (n : ℕ) : PMF (Graph n) :=
  evolve (completeGraph n) (n.choose 2)

noncomputable def expectation (n : ℕ) (f : Graph n → ℝ) : ℝ :=
  ∑ G, (terminalLaw n G).toReal * f G

noncomputable def probability (n : ℕ) (P : Graph n → Prop) : ℝ := by
  classical
  exact expectation n (fun G => if P G then 1 else 0)

noncomputable def normalization (n : ℕ) : ℝ := (n : ℝ) ^ (3 / 2 : ℝ)

noncomputable def normalizedLeave (n : ℕ) (G : Graph n) : ℝ :=
  (G.card : ℝ) / normalization n

noncomputable def sharpConstant : ℝ := 1 / (2 * Real.sqrt 2)

end SharpTerminalLeave
end
end

open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

def sharp_terminal_leave_statement : Prop :=
  Tendsto (fun n => expectation n (fun G =>
      (normalizedLeave n G - sharpConstant) ^ 2)) atTop (𝓝 0) ∧
    (∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => probability n (fun G =>
        ε < |normalizedLeave n G - sharpConstant|)) atTop (𝓝 0)) ∧
    Tendsto (fun n => expectation n (fun G => (G.card : ℝ)) / normalization n)
      atTop (𝓝 sharpConstant)

end SharpTerminalLeave

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.SharpTerminalLeave.sharp_terminal_leave_statement

end Problem

/- Formalization scope, from lean/docs/188.md: Start with the complete graph on $n$ vertices and repeatedly delete the three edges of a uniformly chosen remaining triangle. The formalization proves that the number of edges at termination, divided by $n^{3/2}$, converges in $L^2$ to $1/(2\sqrt2)$. It also states convergence in probability and convergence of the normalized expectation to the same constant. This is the triangle case of the sharp terminal-leave conjecture of Joos and Kühn. -/
