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

- problem_id: ThreeMachine
- collection: openai-math
- question_id: openai-math:124
- source: openai-math
- source_locator: lean/ComparatorChallenges/ThreeMachine.lean#OAI.ThreeMachine.main_theorem
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves the three-processor unit-job scheduling problem of Garey and Johnson: a deterministic polynomial-time algorithm minimizes makespan for nonpreemptive unit-length jobs with arbitrary precedence constraints on three identical parallel machines. For an explicitly given precedence graph, it decides deadline feasibility exactly and constructs a feasible schedule. ([Lean](lean/docs/124.md)) We give a uniform deterministic polynomial-time algorithm for scheduling unit-length jobs with arbitrary precedence constraints on three identical parallel machines. The algorithm constructs a schedule of minimum makespan and decides exactly whether all jobs can finish by a specified deadline. The proof reorganizes feasible schedules into intervals whose job sets have descriptions of bounded size. A dynamic program searches a family containing polynomially many such descriptions. Global boundary conditions and simplification of inherited information keep the descriptions bounded throughout the decomposition.
- notes: OpenAI math result family 124, Polynomial-time scheduling on three identical machines -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/124.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.ThreeMachine.main_theorem
- source_theorem_count: 1
- source_solution_module: OAI.Computability.Scheduling.Main
- source_papers: preprints/A-polynomial-time-algorithm-for-three-machine-unit-job-scheduling-September-24-2026/paper.pdf
- source_scope_note: lean/docs/124.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace ThreeMachine

structure Instance (n : ℕ) where
  edges : List (Fin n × Fin n)

def Instance.edge {n : ℕ} (G : Instance n) (u v : Fin n) : Prop :=
  (u, v) ∈ G.edges

def Instance.acyclic {n : ℕ} (G : Instance n) : Prop :=
  ∀ v, ¬Relation.TransGen G.edge v v

def Feasible {n : ℕ} (G : Instance n) (T : ℕ) (τ : Fin n → ℕ) : Prop :=
  (∀ v, 1 ≤ τ v ∧ τ v ≤ T) ∧
  (∀ t, ((Finset.univ : Finset (Fin n)).filter (fun v => τ v = t)).card ≤ 3) ∧
  ∀ u v, G.edge u v → τ u < τ v

def encodeNat (n : ℕ) : List Bool :=
  let b := Computability.encodeNat n
  List.replicate b.length true ++ false :: b

def encodeList {α : Type} (f : α → List Bool) (xs : List α) : List Bool :=
  encodeNat xs.length ++ xs.flatMap f

def encodeInput {n : ℕ} (G : Instance n) (deadline : Option ℕ) : List Bool :=
  (match deadline with
    | none => [false]
    | some T => true :: encodeNat T) ++
  encodeList encodeNat ((List.range n).map (· + 1)) ++
  encodeList (fun (e : Fin n × Fin n) => encodeNat (e.1.val + 1) ++
    encodeNat (e.2.val + 1)) G.edges

def encodeAnswer : Option (List ℕ) → List Bool
  | none => [false]
  | some slots => true :: encodeList encodeNat slots

def slots {n : ℕ} (τ : Fin n → ℕ) : List ℕ := List.ofFn τ

def CorrectOutput {n : ℕ} (G : Instance n) (deadline : Option ℕ)
    (out : List Bool) : Prop :=
  match deadline with
  | none => ∃ T τ, Feasible G T τ ∧
      (∀ T' τ', Feasible G T' τ' → T ≤ T') ∧
      out = encodeAnswer (some (slots τ))
  | some T =>
      (out = encodeAnswer none ∧ ¬∃ τ, Feasible G T τ) ∨
      ∃ τ, Feasible G T τ ∧ out = encodeAnswer (some (slots τ))

structure Machine (k q g : ℕ) where
  transition : Fin (q + 1) → (Fin (k + 1) → Fin (g + 3)) →
    Option (Fin (q + 1) × (Fin (k + 1) → Fin (g + 3) × Option Turing.Dir))

structure Configuration (k q g : ℕ) where
  state : Fin (q + 1)
  tapes : Fin (k + 1) → Turing.Tape (Fin (g + 3))

def bitSymbol {g : ℕ} (b : Bool) : Fin (g + 3) :=
  if b then ⟨2, by omega⟩ else ⟨1, by omega⟩

def Machine.step {k q g : ℕ} (M : Machine k q g)
    (c : Configuration k q g) : Option (Configuration k q g) := do
  let (state, action) ← M.transition c.state (fun i => (c.tapes i).head)
  return { state := state, tapes := fun i =>
    let tape := (c.tapes i).write (action i).1
    match (action i).2 with
    | none => tape
    | some d => tape.move d }

def Machine.initial {k q g : ℕ} (_M : Machine k q g)
    (input : List Bool) : Configuration k q g :=
  { state := 0, tapes := fun i =>
      Turing.Tape.mk₁ (if i = 0 then input.map bitSymbol else []) }

def Machine.run {k q g : ℕ} (M : Machine k q g) (input : List Bool)
    (t : ℕ) : Configuration k q g :=
  (fun c => (M.step c).getD c)^[t] (M.initial input)

def Machine.Produces {k q g : ℕ} (M : Machine k q g)
    (input out : List Bool) (timeBound : ℕ) : Prop :=
  ∃ t ≤ timeBound, M.step (M.run input t) = none ∧
    ((M.run input t).tapes 0).right₀ = Turing.ListBlank.mk (out.map bitSymbol)

def ReleaseTheorem : Prop :=
  ∃ (k q g : ℕ) (M : Machine k q g) (C : ℕ), 0 < C ∧
    ∀ n (G : Instance n), 1 ≤ n → G.acyclic →
      ∀ deadline : Option ℕ,
        (∀ T ∈ deadline, 1 ≤ T ∧ T ≤ n) →
        ∃ out, CorrectOutput G deadline out ∧
          M.Produces (encodeInput G deadline) out
            (C * ((encodeInput G deadline).length + 2) ^ 150020)

def main_theorem_statement : Prop :=
  ReleaseTheorem

end ThreeMachine

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.ThreeMachine.main_theorem_statement

end Problem

/- Formalization scope, from lean/docs/124.md: The formalization gives a deterministic polynomial-time algorithm for scheduling nonempty collections of unit-length jobs with arbitrary acyclic precedence constraints on three identical parallel machines. It constructs a schedule of minimum makespan and decides exactly whether a valid specified deadline can be met. The algorithm is one fixed finite machine, and its running time is bounded by a polynomial in the binary input length. -/
