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

- problem_id: OneWayLiveness
- collection: openai-math
- question_id: openai-math:129
- source: openai-math
- source_locator: lean/ComparatorChallenges/OneWayLiveness.lean#OAI.OneWayLiveness.main_theorem
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves exponential lower bounds both for complementing two-way nondeterministic finite automata and for simulating one-way nondeterministic automata by two-way deterministic ones. The latter resolves the Sakoda–Sipser state-succinctness conjecture over growing finite alphabets; both results rule out polynomial state bounds independent of alphabet size. ([Lean](lean/docs/129.md)) We prove that two-way nondeterministic finite automata cannot be complemented with a polynomial number of states independent of the alphabet. For each n ≥ 4 we construct an n-state automaton over a finite alphabet whose complement requires at least $`\tfrac12 2^{\lfloor(n-4)/127\rfloor}-1`$ states. One-way liveness on h points accepts a word of binary relations when their ordered product is nonempty. For every h ≥ 2, it has a nondeterministic automaton with $`h+3`$ states and no left moves, whereas every equivalent s-state two-way deterministic automaton satisfies $`4(s+2)^2\ge2^{\lfloor(h-2)/31\rfloor}`$. Partial transition rules, stay moves, and nonaccepting infinite computations are allowed. The alphabets are finite and grow with h, so the result rules out an alphabet-independent polynomial state bound for deterministic two-way simulation, already for one-way nondeterministic sources.
- notes: OpenAI math result family 129, Exponential state costs for two-way automata -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/129.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.OneWayLiveness.main_theorem
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.Automata.Main
- source_main_result: OAI.OneWayLiveness.main_theorem
- source_papers: preprints/An-exponential-state-lower-bound-for-two-way-nondeterministic-complementation-September-25-2026/paper.pdf preprints/An-exponential-two-way-deterministic-state-lower-bound-for-one-way-liveness-September-25-2026/main.pdf
- source_scope_note: lean/docs/129.md
- source_field: Combinatorics
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace OneWayLiveness

@[ext] structure BRel (H : Type*) where
  holds : H → H → Prop

namespace BRel
variable {H : Type*}
instance : One (BRel H) := ⟨⟨Eq⟩⟩
instance : Mul (BRel H) := ⟨fun a b => ⟨fun x z => ∃ y, a.holds x y ∧ b.holds y z⟩⟩
instance : Monoid (BRel H) where
  mul_assoc a b c := by
    ext x z
    change (∃ y, (∃ w, a.holds x w ∧ b.holds w y) ∧ c.holds y z) ↔
      ∃ w, a.holds x w ∧ ∃ y, b.holds w y ∧ c.holds y z
    aesop
  one_mul a := by ext x z; change (∃ y, x = y ∧ a.holds y z) ↔ a.holds x z; simp
  mul_one a := by ext x z; change (∃ y, a.holds x y ∧ y = z) ↔ a.holds x z; simp

/-- Nonemptiness is the existence of a path through the word's ordered product. -/
def live (w : List (BRel H)) : Prop := ∃ x y, w.prod.holds x y
end BRel

abbrev Alphabet (h : ℕ) := BRel (Fin h)
def OWL (h : ℕ) : Set (List (Alphabet h)) := {w | BRel.live w}

inductive Symbol (Alpha : Type*) where
  | left : Symbol Alpha
  | letter : Alpha → Symbol Alpha
  | right : Symbol Alpha

inductive Move where
  | left | stay | right
  deriving DecidableEq

def Move.Rel : Move → ℕ → ℕ → Prop
  | .left, i, j => j + 1 = i
  | .stay, i, j => j = i
  | .right, i, j => j = i + 1

/-- The finite word including both endmarkers. -/
def scanned {Alpha : Type*} (w : List Alpha) (i : Fin (w.length + 2)) : Symbol Alpha :=
  if h0 : i.val = 0 then .left
  else if hi : i.val < w.length + 1 then .letter (w[i.val - 1]'(by omega))
  else .right

abbrev Configuration {Alpha : Type*} (w : List Alpha) (n : ℕ) := Fin (w.length + 2) × Fin n

structure DMachine (Alpha : Type*) (s : ℕ) where
  initial : Fin s
  accepting : Set (Fin s)
  transition : Fin s → Symbol Alpha → Option (Fin s × Move)
  left_boundary : ∀ q q', transition q .left ≠ some (q', .left)
  right_boundary : ∀ q q', transition q .right ≠ some (q', .right)

structure NMachine (Alpha : Type*) (n : ℕ) where
  initial : Fin n
  accepting : Set (Fin n)
  transition : Fin n → Symbol Alpha → Set (Fin n × Move)
  left_boundary : ∀ q q', (q', .left) ∉ transition q .left
  right_boundary : ∀ q q', (q', .right) ∉ transition q .right

def DMachine.Step {Alpha : Type*} {s : ℕ} (M : DMachine Alpha s) (w : List Alpha)
    (c c' : Configuration w s) : Prop :=
  ∃ d, M.transition c.2 (scanned w c.1) = some (c'.2, d) ∧ d.Rel c.1.val c'.1.val

def NMachine.Step {Alpha : Type*} {n : ℕ} (M : NMachine Alpha n) (w : List Alpha)
    (c c' : Configuration w n) : Prop :=
  ∃ d, (c'.2, d) ∈ M.transition c.2 (scanned w c.1) ∧ d.Rel c.1.val c'.1.val

/-- The positive convention explicitly excludes a length-zero computation. -/
def FiniteRun {C : Type*} (positive : Bool) (step : C → C → Prop) (c c' : C) : Prop :=
  if positive then Relation.TransGen step c c' else Relation.ReflTransGen step c c'

def DMachine.Accepts {Alpha : Type*} {s : ℕ} (M : DMachine Alpha s)
    (positive : Bool) (w : List Alpha) : Prop :=
  ∃ c, FiniteRun positive (M.Step w) (⟨0, by omega⟩, M.initial) c ∧ c.2 ∈ M.accepting

def NMachine.Accepts {Alpha : Type*} {n : ℕ} (M : NMachine Alpha n)
    (positive : Bool) (w : List Alpha) : Prop :=
  ∃ c, FiniteRun positive (M.Step w) (⟨0, by omega⟩, M.initial) c ∧ c.2 ∈ M.accepting

def NMachine.NoLeft {Alpha : Type*} {n : ℕ} (M : NMachine Alpha n) : Prop :=
  ∀ q a q', (q', Move.left) ∉ M.transition q a

def NMachine.Recognizes {Alpha : Type*} {n : ℕ} (M : NMachine Alpha n)
    (positive : Bool) (L : Set (List Alpha)) : Prop := ∀ w, M.Accepts positive w ↔ w ∈ L

def DMachine.Recognizes {Alpha : Type*} {s : ℕ} (M : DMachine Alpha s)
    (positive : Bool) (L : Set (List Alpha)) : Prop := ∀ w, M.Accepts positive w ↔ w ∈ L

def main_theorem_statement : Prop :=
  ∀ (h : ℕ) (hh : 2 ≤ h),
    (∃ N : NMachine (Alphabet h) (h + 3), N.NoLeft ∧
      ∀ positive : Bool, N.Recognizes positive (OWL h)) ∧
    (∀ (positive : Bool) (s : ℕ) (D : DMachine (Alphabet h) s),
      D.Recognizes positive (OWL h) →
      2 ^ ((h - 2) / 31) ≤ 4 * (s + if positive then 2 else 1) ^ 2)

end OneWayLiveness

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.OneWayLiveness.main_theorem_statement

end Problem

/- Formalization scope, from lean/docs/129.md: The paper asks how many states are needed to complement or determinize two-way nondeterministic finite automata. The formalization gives, for every $n\ge4$, an explicit $n$-state automaton whose complement requires at least $\tfrac12 2^{\lfloor(n-4)/127\rfloor}-1$ states. For the same family of relational languages and every $n\ge131$, every equivalent deterministic two-way automaton requires at least $\tfrac12 2^{\lfloor(n-4)/127\rfloor}$ states. The alphabet grows with $n$, so neither complementation nor determinization has a polynomial state bound uniform over alphabets. The model has two endmarkers, left, right, and stay moves, and acceptance by a finite run. The separate results about one-way liveness and the Sakoda–Sipser problem are outside this scope. The formalization gives a family of one-way nondeterministic automata with $h+3$ states whose languages require exponentially many states for two-way deterministic recognition. For every $h\ge2$, a deterministic recognizer with $s$ states satisfies $2^{\lfloor(h-2)/31\rfloor}\le4(s+2)^2$ under both acceptance conventions considered in the paper; one convention has the sharper factor $4(s+1)^2$. The alphabet may grow with $h$, so no alphabet-independent polynomial simulation bound holds. -/
