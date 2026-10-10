import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Basic
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

- problem_id: ThompsonNonamenability
- collection: openai-math
- question_id: openai-math:248
- source: openai-math
- source_locator: lean/ComparatorChallenges/ThompsonNonamenability.lean#OAI.ThompsonNonamenability.thompson_F_nonamenable_composition
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that Thompson's group F, the group of dyadic piecewise linear homeomorphisms of the interval, is nonamenable, resolving its longstanding amenability problem. ([Lean](lean/docs/248.md)) We prove that Thompson's group F is nonamenable. This confirms Geoghegan's conjecture and resolves the amenability problem for F.
- notes: OpenAI math result family 248, Thompson's group <i>F</i> is nonamenable -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/248.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.ThompsonNonamenability.thompson_F_nonamenable_composition
- source_theorem_count: 1
- source_solution_module: OAI.GroupTheory.Thompson.Main
- source_main_result: OAI.ThompsonNonamenability.thompson_F_nonamenable_composition
- source_papers: preprints/Thompsons-group-F-is-nonamenable-September-23-2026/paper.pdf
- source_scope_note: lean/docs/248.md
- source_field: GroupTheory
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open scoped ENNReal

universe uG

namespace ThompsonNonamenability

abbrev UnitInterval := Set.Icc (0 : ℝ) 1

def unitIntervalZero : UnitInterval := ⟨0, le_rfl, zero_le_one⟩
def unitIntervalOne : UnitInterval := ⟨1, zero_le_one, le_rfl⟩

structure IntervalHomeomorph where
  toHomeomorph : UnitInterval ≃ₜ UnitInterval

namespace IntervalHomeomorph

instance : CoeFun IntervalHomeomorph (fun _ => UnitInterval → UnitInterval) :=
  ⟨fun f => f.toHomeomorph⟩

end IntervalHomeomorph

def IsDyadic (x : ℝ) : Prop :=
  ∃ (k : ℤ) (n : ℕ), x = (k : ℝ) / (2 : ℝ) ^ n

structure DyadicPLWitness (f : IntervalHomeomorph) where
  pieceCount : ℕ
  positive : 0 < pieceCount
  knots : Fin (pieceCount + 1) → UnitInterval
  strictMono_knots : StrictMono knots
  first : knots 0 = unitIntervalZero
  last : knots (Fin.last pieceCount) = unitIntervalOne
  dyadic : ∀ i, IsDyadic (knots i : ℝ)
  cover : ∀ x : UnitInterval, ∃ i : Fin pieceCount,
    knots i.castSucc ≤ x ∧ x ≤ knots i.succ
  exponent : Fin pieceCount → ℤ
  affine : ∀ (i : Fin pieceCount) (x : UnitInterval),
    knots i.castSucc ≤ x → x ≤ knots i.succ →
    (f x : ℝ) = (f (knots i.castSucc) : ℝ) +
      (2 : ℝ) ^ exponent i * ((x : ℝ) - (knots i.castSucc : ℝ))

def HasDyadicPLPieces (f : IntervalHomeomorph) : Prop := Nonempty (DyadicPLWitness f)

def F := {f : IntervalHomeomorph // StrictMono f ∧ HasDyadicPLPieces f}

abbrev BoundedReal (G : Type uG) := lp (fun _ : G => ℝ) ∞

variable {G : Type uG} [Group G]

def leftPull (h : G) : BoundedReal G →ₗ[ℝ] BoundedReal G where
  toFun f := ⟨fun g => f (h * g), memℓp_infty ⟨‖f‖, by
    rintro y ⟨g, rfl⟩
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero f (h * g)⟩⟩
  map_add' f g := by
    apply lp.ext
    funext x
    rfl
  map_smul' r f := by
    apply lp.ext
    funext x
    rfl

structure InvariantMean (G : Type uG) [Group G] where
  toLinearMap : BoundedReal G →ₗ[ℝ] ℝ
  positive : ∀ f : BoundedReal G, (∀ g, 0 ≤ f g) → 0 ≤ toLinearMap f
  normalized : toLinearMap 1 = 1
  left_invariant : ∀ (h : G) (f : BoundedReal G),
    toLinearMap (leftPull h f) = toLinearMap f

def thompson_F_nonamenable_composition_statement : Prop :=
  ∃ group : Group F, letI := group;
      (∀ (h g : F) (x : UnitInterval),
        (h * g).val.toHomeomorph x = h.val.toHomeomorph (g.val.toHomeomorph x)) ∧
      ¬ Nonempty (InvariantMean F)

end ThompsonNonamenability

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.ThompsonNonamenability.thompson_F_nonamenable_composition_statement

end Problem

/- Formalization scope, from lean/docs/248.md: The amenability problem for Thompson's group $F$ asks whether it admits a positive normalized left-invariant mean on bounded real functions. The formalized result rules out such a mean for the standard group of dyadic piecewise-linear homeomorphisms of the interval, proving nonamenability. No explicit boundary constant or prescribed generating set is given. -/
