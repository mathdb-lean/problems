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

- problem_id: QuinticLienard
- collection: openai-math
- question_id: openai-math:143
- source: openai-math
- source_locator: lean/ComparatorChallenges/QuinticLienard.lean#OAI.QuinticLienard.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves the uniform boundedness assertion in Hilbert's sixteenth problem: the number of isolated periodic orbits of a real planar polynomial vector field is bounded by a finite constant depending only on its degree. For classical quintic Liénard systems, the exact maximum is two limit cycles. ([Lean](lean/docs/143.md)) Every classical Liénard system $`\dot x=y-F(x)`$, $`\dot y=-x`$, with F an arbitrary real polynomial of degree at most five, has at most two geometrically distinct isolated periodic orbits, and the bound is attained. This proves the degree-five case of the Lins Neto–de Melo–Pugh conjecture.
- notes: OpenAI math result family 143, Hilbert's sixteenth problem: uniform bounds for limit cycles -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/143.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.QuinticLienard.main
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.LienardCycles.Main
- source_main_result: OAI.QuinticLienard.main
- source_papers: preprints/two-limit-cycles-for-quintic-lienard-systems-September-24-2026/two-limit-cycles-for-quintic-lienard-systems-September-24-2026.pdf
- source_scope_note: lean/docs/143.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace QuinticLienard

abbrev Plane := ℝ × ℝ

def vectorField (F : Polynomial ℝ) (z : Plane) : Plane :=
  (z.2 - F.eval z.1, -z.1)

def IsSolution (F : Polynomial ℝ) (z : ℝ → Plane) : Prop :=
  ∀ t : ℝ, HasDerivAt z (vectorField F (z t)) t

def IsPeriodicOrbit (F : Polynomial ℝ) (C : Set Plane) : Prop :=
  ∃ (z : ℝ → Plane) (T : ℝ),
    IsSolution F z ∧ 0 < T ∧ Function.Periodic z T ∧
    (∃ s t : ℝ, z s ≠ z t) ∧ C = Set.range z

def IsLimitCycle (F : Polynomial ℝ) (C : Set Plane) : Prop :=
  IsPeriodicOrbit F C ∧
    ∃ U : Set Plane, IsOpen U ∧ C ⊆ U ∧
      ∀ C' : Set Plane, IsPeriodicOrbit F C' → C' ⊆ U → C' = C

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff NNReal

def main_statement : Prop :=
  (∀ F : Polynomial ℝ, F.degree ≤ 5 → {C : Set Plane | IsLimitCycle F C}.encard ≤ 2) ∧
    (∃ F : Polynomial ℝ, F.degree ≤ 5 ∧ {C : Set Plane | IsLimitCycle F C}.encard = 2)

end QuinticLienard

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.QuinticLienard.main_statement

end Problem

/- Formalization scope, from lean/docs/143.md: For the quintic Liénard system $x'=y-F(x)$, $y'=-x$, the formalized result proves that every real polynomial $F$ of degree at most five yields at most two limit cycles, and that some such $F$ yields exactly two. Limit cycles are isolated images of nonconstant periodic solutions. No sign, parity, hyperbolicity, or amplitude restriction is imposed. -/
