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

- problem_id: TwoWayDeterminization
- collection: openai-math
- question_id: openai-math:129
- source: openai-math
- source_locator: lean/ComparatorChallenges/TwoWayDeterminization.lean#OAI.TwoWayComplementation.explicit_family_main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves exponential lower bounds both for complementing two-way nondeterministic finite automata and for simulating one-way nondeterministic automata by two-way deterministic ones. The latter resolves the Sakoda–Sipser state-succinctness conjecture over growing finite alphabets; both results rule out polynomial state bounds independent of alphabet size. ([Lean](lean/docs/129.md)) We prove that two-way nondeterministic finite automata cannot be complemented with a polynomial number of states independent of the alphabet. For each n ≥ 4 we construct an n-state automaton over a finite alphabet whose complement requires at least $`\tfrac12 2^{\lfloor(n-4)/127\rfloor}-1`$ states. One-way liveness on h points accepts a word of binary relations when their ordered product is nonempty. For every h ≥ 2, it has a nondeterministic automaton with $`h+3`$ states and no left moves, whereas every equivalent s-state two-way deterministic automaton satisfies $`4(s+2)^2\ge2^{\lfloor(h-2)/31\rfloor}`$. Partial transition rules, stay moves, and nonaccepting infinite computations are allowed. The alphabets are finite and grow with h, so the result rules out an alphabet-independent polynomial state bound for deterministic two-way simulation, already for one-way nondeterministic sources.
- notes: OpenAI math result family 129, Exponential state costs for two-way automata -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/129.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.TwoWayComplementation.explicit_family_main
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.TwoWayAutomata.ExplicitFamily
- source_main_result: OAI.TwoWayComplementation.explicit_family_main
- source_papers: preprints/An-exponential-state-lower-bound-for-two-way-nondeterministic-complementation-September-25-2026/paper.pdf preprints/An-exponential-two-way-deterministic-state-lower-bound-for-one-way-liveness-September-25-2026/main.pdf
- source_scope_note: lean/docs/129.md
- source_field: Combinatorics
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Reflexive transitive closure, including the empty path. -/
def relStar {α : Type*} (R : SetRel α α) : SetRel α α :=
  {(x, y) | Relation.ReflTransGen (fun a b => (a, b) ∈ R) x y}

/-- A read-only 2NFA. The two endmarkers are `Sum.inl 0` and `Sum.inl 1`.
    Move codes 0, 1, 2 mean left, stay, right. -/
structure TwoNFA (Sigma Q : Type*) where
  /-- The state in which the machine starts on the left endmarker. -/
  initial : Q
  /-- States whose occurrence on a finite run constitutes acceptance. -/
  accepting : Set Q
  /-- Allowed next-state and move pairs, determined by the state and scanned symbol. -/
  transition : Q → (Fin 2 ⊕ Sigma) → Set (Q × Fin 3)

/-- Tape lookup includes two distinct endmarkers, even on empty input. -/
def tapeSymbol {Sigma : Type*} (w : List Sigma) (p : Fin (w.length + 2)) : Fin 2 ⊕ Sigma :=
  if hleft : p.val = 0 then .inl 0
  else if hright : p.val = w.length + 1 then .inl 1
  else .inr (w[p.val - 1]'(by omega))

namespace TwoNFA

/-- One legal step: both head positions stay within the marked input. -/
def step {Sigma Q : Type*} (A : TwoNFA Sigma Q) (w : List Sigma) :
    SetRel (Q × Fin (w.length + 2)) (Q × Fin (w.length + 2)) :=
  {(c, d) | ∃ move : Fin 3,
    (d.1, move) ∈ A.transition c.1 (tapeSymbol w c.2) ∧
    (d.2.val : ℤ) = (c.2.val : ℤ) + (move.val : ℤ) - 1}

/-- Existential finite-run acceptance, allowing a run of length zero. -/
def language {Sigma Q : Type*} (A : TwoNFA Sigma Q) : Set (List Sigma) :=
  {w | ∃ c, c.1 ∈ A.accepting ∧
    ((A.initial, ⟨0, by omega⟩), c) ∈ relStar (A.step w)}

end TwoNFA

/-- At most one next-state/move pair at every state and scanned symbol. -/
def TwoNFA.Deterministic {Sigma Q : Type*} (A : TwoNFA Sigma Q) : Prop :=
  ∀ q symbol, (A.transition q symbol).Subsingleton

/-- Relation product for an input word; the empty product is the identity. -/
def relationProduct {H : Type*} (w : List (SetRel H H)) : SetRel H H :=
  w.foldr SetRel.comp SetRel.id

/-- The source language consists of the words with nonempty relation product. -/
def sourceLanguage (H : Type*) : Set (List (SetRel H H)) :=
  {w | (relationProduct w).Nonempty}

/-- Both lower bounds hold for the same n-state liveness witness. -/
def explicit_family_main_statement : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n),
    ∃ A : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) (Fin n),
      A.language = sourceLanguage (Fin (n - 2)) ∧
      (∀ (Q : Type*) [Fintype Q],
        ∀ B : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) Q,
        B.language = A.languageᶜ →
          (1 / 2 : ℝ) * 2 ^ ((n - 4) / 127) - 1 ≤ (Fintype.card Q : ℝ)) ∧
      (131 ≤ n → ∀ (Q : Type*) [Fintype Q],
        ∀ D : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) Q,
        D.Deterministic → D.language = A.language →
          (1 / 2 : ℝ) * 2 ^ ((n - 4) / 127) ≤ (Fintype.card Q : ℝ))

end TwoWayComplementation

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u_1, u_2} : Prop :=
  _root_.OAI.TwoWayComplementation.explicit_family_main_statement.{u_1, u_2}

end Problem

/- Formalization scope, from lean/docs/129.md: The paper asks how many states are needed to complement or determinize two-way nondeterministic finite automata. The formalization gives, for every $n\ge4$, an explicit $n$-state automaton whose complement requires at least $\tfrac12 2^{\lfloor(n-4)/127\rfloor}-1$ states. For the same family of relational languages and every $n\ge131$, every equivalent deterministic two-way automaton requires at least $\tfrac12 2^{\lfloor(n-4)/127\rfloor}$ states. The alphabet grows with $n$, so neither complementation nor determinization has a polynomial state bound uniform over alphabets. The model has two endmarkers, left, right, and stay moves, and acceptance by a finite run. The separate results about one-way liveness and the Sakoda–Sipser problem are outside this scope. The formalization gives a family of one-way nondeterministic automata with $h+3$ states whose languages require exponentially many states for two-way deterministic recognition. For every $h\ge2$, a deterministic recognizer with $s$ states satisfies $2^{\lfloor(h-2)/31\rfloor}\le4(s+2)^2$ under both acceptance conventions considered in the paper; one convention has the sharper factor $4(s+1)^2$. The alphabet may grow with $h$, so no alphabet-independent polynomial simulation bound holds. -/
