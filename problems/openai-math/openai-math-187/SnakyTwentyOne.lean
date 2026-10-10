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

- problem_id: SnakyTwentyOne
- collection: openai-math
- question_id: openai-math:187
- source: openai-math
- source_locator: lean/ComparatorChallenges/SnakyTwentyOne.lean#OAI.SnakyPrototype.snaky_winning_strategy_21_with_legal_states
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Settles the Snaky achievement problem: Maker can force the six-cell Snaky shape within 21 of its own moves on the initially empty infinite square board. Maker moves first, each player claims one free cell per turn, and translations, rotations and reflections count as wins. ([Lean](lean/docs/187.md)) We prove that Maker can achieve the Snaky hexomino within 21 actual Maker moves against arbitrary legal Breaker play on the initially empty infinite square board. The same bound holds on a $`17\times17`$ square; in fact, Maker can confine its claims to a fixed 251-cell board.
- notes: OpenAI math result family 187, Snaky in 21 Maker moves -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/187.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.SnakyPrototype.snaky_winning_strategy_21_with_legal_states
- source_theorem_count: 1
- source_solution_module: OAI.GameTheory.SnakyTwentyOne.Main
- source_papers: preprints/Snaky-in-21-Maker-moves-September-25-2026/article.pdf
- source_scope_note: lean/docs/187.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace SnakyPrototype
variable {α : Type*} [DecidableEq α]
abbrev Cell := ℤ × ℤ
def snaky : Finset Cell := {(0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (4, 1)}
def orient (r : Fin 8) (p : Cell) : Cell :=
  match r.val with
  | 0 => (p.1, p.2)
  | 1 => (p.2, p.1)
  | 2 => (p.1, -p.2)
  | 3 => (-p.2, p.1)
  | 4 => (-p.1, p.2)
  | 5 => (p.2, -p.1)
  | 6 => (-p.1, -p.2)
  | _ => (-p.2, -p.1)
def placement (r : Fin 8) (t p : Cell) : Cell := orient r p + t
def HasSnaky (M : Finset Cell) : Prop :=
  ∃ (r : Fin 8) (t : Cell), snaky.image (placement r t) ⊆ M
end SnakyPrototype
namespace SnakyPrototype.OrdinaryStrategy
variable {α : Type*} [DecidableEq α] [Infinite α]
abbrev Policy (α : Type*) := ℕ → Finset α → Finset α → α
def playState (σ : Policy α) (N : ℕ) (β : ℕ → α) (M₀ B₀ : Finset α) :
    ℕ → Finset α × Finset α
  | 0 => (M₀, B₀)
  | k + 1 =>
      let state := playState σ N β M₀ B₀ k
      (insert (σ (N - k) state.1 state.2) state.1, insert (β k) state.2)
def makerAt (σ : Policy α) (N : ℕ) (β : ℕ → α) (M₀ B₀ : Finset α) (k : ℕ) : α :=
  let state := playState σ N β M₀ B₀ k
  σ (N - k) state.1 state.2
def LegalRepliesBeforeFinal (σ : Policy α) (N : ℕ) (β : ℕ → α)
    (M₀ B₀ : Finset α) : Prop :=
  ∀ k, k + 1 < N →
    β k ∉ insert (makerAt σ N β M₀ B₀ k) (playState σ N β M₀ B₀ k).1 ∧
    β k ∉ (playState σ N β M₀ B₀ k).2
end SnakyPrototype.OrdinaryStrategy

namespace SnakyPrototype
open OrdinaryStrategy

def snaky_winning_strategy_21_with_legal_states_statement : Prop :=
  ∃ σ : Policy Cell,
      (∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B) ∧
      ∀ β : ℕ → Cell, LegalRepliesBeforeFinal σ 21 β ∅ ∅ →
        HasSnaky (playState σ 21 β ∅ ∅ 21).1 ∧
        (playState σ 21 β ∅ ∅ 21).1.card = 21 ∧
        Disjoint (playState σ 21 β ∅ ∅ 21).1 (playState σ 21 β ∅ ∅ 20).2 ∧
        ∀ k, k < 21 →
          Disjoint (playState σ 21 β ∅ ∅ k).1 (playState σ 21 β ∅ ∅ k).2 ∧
          (playState σ 21 β ∅ ∅ k).2.card = k

end SnakyPrototype

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.SnakyPrototype.snaky_winning_strategy_21_with_legal_states_statement

end Problem

/- Formalization scope, from lean/docs/187.md: In the Snaky Maker–Breaker game, the players alternately claim cells of $\mathbb Z^2$, and Maker seeks a translated, rotated, or reflected copy of the six-cell Snaky shape. The formalization gives a legal strategy that wins within $21$ actual Maker moves against every legal Breaker play from the empty infinite board. The selected theorem checks disjointness and the move counts throughout play; it does not impose the paper's smaller finite-board restriction. The linked supplements reconstruct the older $35$-move appendix's finite recursive certificate and prove four conditional winning templates from partial positions, assuming the required Maker cells are present and Breaker avoids the corresponding finite envelope. -/
