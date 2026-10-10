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

- problem_id: HenonEmden
- collection: openai-math
- question_id: openai-math:370
- source: openai-math
- source_locator: lean/ComparatorChallenges/HenonEmden.lean#OAI.HenonLaneEmden.main_nonexistence
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves the subcritical Lane–Emden conjecture and its weighted Hénon extension. For n ≥ 2, $`p,q\gt 0`$ and real A, B, the system $`-\Delta u=|x|^A v^p`$, $`-\Delta v=|x|^B u^q`$ has no positive entire solution when $`(n+A)/(p+1)+(n+B)/(q+1)\gt n-2`$, with solutions continuous at the origin and classical elsewhere. No symmetry or growth assumption is needed. Known radial existence gives the exact existence criterion for n ≥ 3 and $`A,B\gt -2`$. ([Lean](lean/docs/370.md)) We prove the subcritical Hénon–Lane–Emden conjecture: for every dimension n ≥ 2, positive powers p, q, and real weights A, B, the system has no strictly positive entire solution when $`(n+A)/(p+1)+(n+B)/(q+1)\gt n-2`$. Solutions need only be continuous at the origin and classical elsewhere, without a condition at infinity. For n ≥ 3 and $`A,B\gt -2`$, combining this result with the radial existence theorem of Bidaut-Véron and Giacomini proves Phan's Conjecture C in full: a positive radial entire solution exists whenever the strict inequality fails.
- notes: OpenAI math result family 370, The Lane–Emden and Hénon–Lane–Emden conjectures -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/370.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.HenonLaneEmden.main_nonexistence
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.HenonEmden.Main
- source_main_result: OAI.HenonLaneEmden.main_nonexistence
- source_papers: preprints/The-Subcritical-Henon-Lane-Emden-Conjecture-September-24-2026/paper.pdf
- source_scope_note: lean/docs/370.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace HenonLaneEmden

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

structure IsSolution (n : ℕ) (p q A B : ℝ) (u v : Space n → ℝ) : Prop where
  continuous_u : Continuous u
  continuous_v : Continuous v
  regular_u : ContDiffOn ℝ 2 u ({0}ᶜ : Set (Space n))
  regular_v : ContDiffOn ℝ 2 v ({0}ᶜ : Set (Space n))
  positive_u : ∀ x, 0 < u x
  positive_v : ∀ x, 0 < v x
  equation_u : ∀ x, x ≠ 0 →
    -(Laplacian.laplacian u) x = Real.rpow ‖x‖ A * Real.rpow (v x) p
  equation_v : ∀ x, x ≠ 0 →
    -(Laplacian.laplacian v) x = Real.rpow ‖x‖ B * Real.rpow (u x) q

def Subcritical (n : ℕ) (p q A B : ℝ) : Prop :=
  ((n : ℝ) + A) / (p + 1) + ((n : ℝ) + B) / (q + 1) > (n : ℝ) - (1 + 1)

def main_nonexistence_statement : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (p q A B : ℝ) (hp : 0 < p) (hq : 0 < q) (hsub : Subcritical n p q A B),
    ¬ ∃ u v : Space n → ℝ, IsSolution n p q A B u v

end HenonLaneEmden

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.HenonLaneEmden.main_nonexistence_statement

end Problem

/- Formalization scope, from lean/docs/370.md: The formalized result proves nonexistence of positive entire solutions to the subcritical Hénon–Lane–Emden system. For $n\ge2$, $p,q>0$, and real $A,B$ with $(n+A)/(p+1)+(n+B)/(q+1)>n-2$, there are no positive functions, continuous everywhere and $C^2$ off the origin, satisfying $-\Delta u=|x|^A v^p$ and $-\Delta v=|x|^B u^q$ away from the origin. It includes the globally $C^2$ unweighted case for $n\ge3$. The critical equality case is not included. -/
