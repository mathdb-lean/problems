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

- problem_id: MatroidProphet
- collection: openai-math
- question_id: openai-math:111
- source: openai-math
- source_locator: lean/ComparatorChallenges/MatroidProphet.lean#OAI.MatroidProphet.one_sample
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: For every finite matroid known in advance, gives a distribution-independent online rule using one independent sample per element and earning a universal constant fraction of the expected offline optimum. Values are independent and nonnegative, with finite expected optimum. The guarantee holds even when the arrival-order adversary sees all samples, values, and the rule's entire random seed; no polynomial-time implementation is asserted. ([Lean](lean/docs/111.md)) We prove that one independent sample per element suffices for a constant-competitive prophet inequality on every finite matroid. The guarantee holds even when the arrival-order adversary observes all samples, all online values, and the algorithm's entire random seed. The rule needs no description of the value distributions and achieves the absolute competitive ratio $`2^{-310}`$.
- notes: OpenAI math result family 111, One-sample matroid prophet inequalities against an almighty adversary -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/111.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.MatroidProphet.one_sample
- source_theorem_count: 1
- source_solution_module: OAI.Probability.MatroidProphet.Main
- source_papers: preprints/One-Sample-Suffices-for-Matroid-Prophet-Inequalities-against-an-Almighty-Adversary-September-23-2026/final.pdf
- source_scope_note: lean/docs/111.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-!
# One-sample matroid selection

The rule and its finite seed law depend only on the known labeled matroid.
A decision sees the initial sample vector, the entire seed, and the arriving
label/value prefix. Every prefix is feasible, and decisions are irrevocable.
The arrival permutation may depend on all samples, values, and seed bits.
Only the actual offline optimum is required to be integrable.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace MatroidProphet

abbrev Weights (n : ℕ) := Fin n → ℝ
abbrev Seed (bits : ℕ) := Fin bits → Bool
abbrev ArrivalOrder (n : ℕ) := Equiv.Perm (Fin n)
instance arrivalOrderMeasurableSpace (n : ℕ) : MeasurableSpace (ArrivalOrder n) := ⊤

abbrev History (n : ℕ) (k : Fin n) := Fin (k.val + 1) → Fin n × ℝ

structure OnlineRule (n bits : ℕ) where
  decide : (k : Fin n) → Seed bits → Weights n → History n k → Bool
  measurable_decide : ∀ k, Measurable
    (fun x : Seed bits × (Weights n × History n k) => decide k x.1 x.2.1 x.2.2)

def prefixIndex {n : ℕ} (k : Fin n) (j : Fin (k.val + 1)) : Fin n :=
  ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩

def history {n : ℕ} (v : Weights n) (π : ArrivalOrder n) (k : Fin n) : History n k :=
  fun j => let e := π (prefixIndex k j); (e, v e)

def decisionAt {n bits : ℕ} (A : OnlineRule n bits) (r : Seed bits)
    (s v : Weights n) (π : ArrivalOrder n) (k : Fin n) : Bool :=
  A.decide k r s (history v π k)

noncomputable def acceptedThrough {n bits : ℕ} (A : OnlineRule n bits) (r : Seed bits)
    (s v : Weights n) (π : ArrivalOrder n) (t : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun e =>
    (π.symm e).val < t ∧ decisionAt A r s v π (π.symm e) = true

noncomputable def accepted {n bits : ℕ} (A : OnlineRule n bits) (r : Seed bits)
    (s v : Weights n) (π : ArrivalOrder n) : Finset (Fin n) :=
  acceptedThrough A r s v π n

noncomputable def reward {n bits : ℕ} (A : OnlineRule n bits) (r : Seed bits)
    (s v : Weights n) (π : ArrivalOrder n) : ℝ :=
  ∑ e ∈ accepted A r s v π, v e

noncomputable def optimum {n : ℕ} (M : Matroid (Fin n)) (v : Weights n) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty
    (fun I : Finset (Fin n) => if M.Indep (I : Set (Fin n)) then ∑ e ∈ I, v e else 0)

def Feasible {n bits : ℕ} (M : Matroid (Fin n)) (A : OnlineRule n bits) : Prop :=
  ∀ (r : Seed bits) (s v : Weights n) (π : ArrivalOrder n) (t : ℕ),
    (∀ e, 0 ≤ s e) → (∀ e, 0 ≤ v e) →
    M.Indep (acceptedThrough A r s v π t : Set (Fin n))

def pairedCoordinates.{u} {n : ℕ} {Ω : Type u} (S V : Ω → Weights n)
    (i : Fin n × Bool) : Ω → ℝ :=
  if i.2 then fun ω => S ω i.1 else fun ω => V ω i.1

def OneSampleChallenge.{u} : Prop :=
  ∀ (n : ℕ) (M : Matroid (Fin n)), M.E = Set.univ →
    ∃ (bits : ℕ) (ν : Measure (Seed bits)), IsProbabilityMeasure ν ∧
    ∃ (A : OnlineRule n bits), Feasible M A ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (S V : Ω → Weights n) (R : Ω → Seed bits),
        Measurable S → Measurable V → Measurable R →
        (∀ᵐ ω ∂μ, ∀ e, 0 ≤ S ω e) →
        (∀ᵐ ω ∂μ, ∀ e, 0 ≤ V ω e) →
        iIndepFun (pairedCoordinates S V) μ →
        (∀ e, Measure.map (fun ω => S ω e) μ = Measure.map (fun ω => V ω e) μ) →
        IndepFun (fun ω => (S ω, V ω)) R μ →
        Measure.map R μ = ν →
        Integrable (fun ω => optimum M (V ω)) μ →
        ∀ (π : Ω → ArrivalOrder n), Measurable π →
          Integrable (fun ω => reward A (R ω) (S ω) (V ω) (π ω)) μ ∧
          ((2 : ℝ) ^ 310)⁻¹ * (∫ ω, optimum M (V ω) ∂μ) ≤
            ∫ ω, reward A (R ω) (S ω) (V ω) (π ω) ∂μ

def one_sample_statement.{u} : Prop :=
  OneSampleChallenge.{u}

end MatroidProphet

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.MatroidProphet.one_sample_statement.{u}

end Problem

/- Formalization scope, from lean/docs/111.md: The formalization proves a one-sample matroid prophet inequality with expected reward at least $2^{-310}$ times the expected offline optimum. Each element has one independent sample paired with an identically distributed nonnegative online value, and all coordinates are independent. The rule and finite seed law depend only on the labeled matroid; choices are irrevocable and feasible after every prefix. The arrival order may depend measurably on all samples, values, and the seed, and only the offline optimum must be integrable. A supporting hidden-vector selection result for fixed nonnegative matroid weights gives expected worst-order reward at least $2^{-293}$ times the optimum, again with a finite seed law and prefix feasibility. -/
