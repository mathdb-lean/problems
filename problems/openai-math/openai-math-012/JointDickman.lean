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

- problem_id: JointDickman
- collection: openai-math
- question_id: openai-math:012
- source: openai-math
- source_locator: lean/ComparatorChallenges/JointDickman.lean#OAI.JointDickmanPaper.joint_law
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves the Erdős–Pomerance joint Dickman conjecture: the logarithmic sizes of the largest prime factors of n and $`n+1`$ are asymptotically independent in ordinary natural density. In particular, the integers satisfying $`P^+(n)\lt P^+(n+1)`$ have density 1/2. ([Lean](lean/docs/012.md)) Let $`P^+(n)`$ denote the largest prime factor of n. We prove that $`\log P^+(n)/\log n`$ and $`\log P^+(n+1)/\log n`$ are asymptotically independent in ordinary natural density, with Dickman marginals. This resolves the Erdős–Pomerance joint Dickman conjecture positively and implies that the ordering $`P^+(n)\lt P^+(n+1)`$ has natural density 1/2.
- notes: OpenAI math result family 012, Independent largest prime factors of consecutive integers -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/012.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.JointDickmanPaper.joint_law OAI.JointDickmanPaper.increasing_order OAI.JointDickmanPaper.decreasing_order
- source_theorem_count: 3
- source_solution_module: OAI.NumberTheory.JointDickman.PaperMain
- source_papers: preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf
- source_scope_note: lean/docs/012.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-! # The joint Dickman law for consecutive integers -/

namespace Erdos970.NumberTheoryLean.DelayConstruction

noncomputable def kernel (f : ℝ → ℝ) (t : ℝ) : ℝ := f (t - 1) / max 1 t

noncomputable def stepApprox (σ : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | n + 1 => fun u => 1 + σ * ∫ t in (1 : ℝ)..max 1 u, kernel (stepApprox σ n) t

noncomputable def delay (σ u : ℝ) : ℝ := stepApprox σ ⌈u⌉₊ u

end Erdos970.NumberTheoryLean.DelayConstruction

namespace Erdos970.NumberTheoryLean.Dickman

/-- The continuous delay-equation construction of the Dickman function. -/
noncomputable def rho : ℝ → ℝ := DelayConstruction.delay (-1)

end Erdos970.NumberTheoryLean.Dickman

namespace JointDickman

noncomputable def empiricalCount (P : ℕ → Prop) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 2 N).filter P).card

/-- Ordinary natural density over `2 ≤ n ≤ X`, normalized by the real endpoint. -/
noncomputable def realDensity (P : ℕ → Prop) (X : ℝ) : ℝ :=
  (empiricalCount P ⌊X⌋₊ : ℝ) / X

end JointDickman

namespace JointDickmanPaper

open Filter JointDickman
open scoped Topology

/-- Theorem 1: ordinary natural density, with both thresholds based at `n`. -/
def joint_law_statement : Prop :=
  ∀ (a b : ℝ) (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1),
    Tendsto (realDensity (fun n =>
      (n.maxPrimeFac : ℝ) ≤ (n : ℝ) ^ a ∧ ((n + 1).maxPrimeFac : ℝ) ≤ (n : ℝ) ^ b))
      atTop (𝓝 (Erdos970.NumberTheoryLean.Dickman.rho (1 / a) *
        Erdos970.NumberTheoryLean.Dickman.rho (1 / b)))

/-- Corollary 2: the increasing strict ordering has natural density one half. -/
def increasing_order_statement : Prop :=
  Tendsto (realDensity (fun n => n.maxPrimeFac < (n + 1).maxPrimeFac))
      atTop (𝓝 (1 / 2))

/-- The reverse strict ordering also has natural density one half. -/
def decreasing_order_statement : Prop :=
  Tendsto (realDensity (fun n => (n + 1).maxPrimeFac < n.maxPrimeFac))
      atTop (𝓝 (1 / 2))

end JointDickmanPaper

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.JointDickmanPaper.joint_law_statement ∧
  _root_.OAI.JointDickmanPaper.increasing_order_statement ∧
  _root_.OAI.JointDickmanPaper.decreasing_order_statement

end Problem

/- Formalization scope, from lean/docs/012.md: Let $P^+(n)$ be the largest prime factor of $n$. The formalization proves the joint Dickman law in ordinary natural density: for every $0<a,b<1$, the density of integers satisfying $P^+(n)\le n^a$ and $P^+(n+1)\le n^b$ tends to $\rho(1/a)\rho(1/b)$, where $\rho$ is the Dickman function. It also proves that each of the orderings $P^+(n)<P^+(n+1)$ and $P^+(n+1)<P^+(n)$ has natural density $1/2$. -/
