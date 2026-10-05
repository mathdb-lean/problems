/-
Copyright 2025 The Formal Conjectures Authors.
Copyright 2026 The mathdb-lean Authors.

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

import MathdbUtil

/-!
Converted from another corpus. `source` names it, `source_version`
pins the revision, and `source_locator` points at the one
declaration this came from. Every `source_` field describes that
declaration as it stands there, not as it stands here.

Read `track` for whether the problem is solved, which is a fact
about mathematics. `source_has_lean_proof` is a different claim --
whether that corpus holds a machine-checked proof -- and is false
for almost every problem, because it is a statement repository.

- problem_id: RCatchUpConjecture_value_of_even_mul_succ_self_div_two
- collection: paper
- question_id: paper:CatchUpConjecture
- source: formal-conjectures
- source_locator: FormalConjectures/Paper/CatchUpConjecture.lean#value_of_even_mul_succ_self_div_two
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $T_N = \sum_{k=1}^{N} k = \frac{N(N+1)}{2}$. If $T_N$ is even (equivalently $N \equiv 0 \pmod 4$ or $N \equiv 3 \pmod 4$), then under optimal play the game `Catch-Up($\{1, \ldots, N\}$)` ends in a draw.
- notes: Problem from CatchUpConjecture
- track: open
- answer_shape: proof
- source_stem: CatchUpConjecture
- source_namespace: CatchUp
- source_theorem: value_of_even_mul_succ_self_div_two
- source_category: research open
- source_ams: 11 91
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
An arbitrary two elements type indexing the players in the Catch-Up game.
-/
inductive Player
  | p1
  | p2
deriving DecidableEq, Repr

/-- Returns the other player. -/
def Player.other : Player → Player
  | p1 => p2
  | p2 => p1

/-- The possible outcomes of a Catch-Up game. -/
inductive Outcome
  | win
  | loss
  | draw
deriving DecidableEq, Repr

/-- Negates an outcome, swapping win and loss. Used when switching player perspectives. -/
def Outcome.neg : Outcome → Outcome
  | win => loss
  | loss => win
  | draw => draw

/--
Computes the best outcome for the current player from a list of possible outcomes.
Win > Draw > Loss.
-/
def Outcome.best (os : List Outcome) : Outcome :=
  os.foldl (fun
    | .win,  _     => .win
    | _,     .win  => .win
    | .draw, _     => .draw
    | _,     .draw => .draw
    | _,     _     => .loss) .loss

/-
Define the recursive game value functions.
-/

/--
`value remaining s_me s_opp isFirstMove` evaluates the position where:

* `remaining` is the set `S'` of numbers not yet taken.
* `s_me` is the current score of the player who is about to act (the “current player”).
* `s_opp` is the opponent’s current score.
* `isFirstMove` indicates whether we are in the special very first move of the whole game,
  where the rules force exactly one pick and then the turn passes.

The result is the game-theoretic value from the current player’s point of view:
`.win` / `.loss` / `.draw`, assuming optimal play from both sides.

We model a single *turn* (which may consist of several picks `$x_1,...,x_k$`) by recursion:
the current player chooses one number `x`; if they are still strictly behind after taking it, they must
continue the same turn (so the recursive call keeps the same “current player”);
once they catch up (score ≥ opponent), the turn ends and we swap players.
-/
noncomputable def valueAux (remaining : Finset ℕ) (s_me s_opp : ℕ) (isFirstMove : Bool) : Outcome :=
  -- If no numbers remain, the game is over. Compare final scores.
  if remaining = ∅ then
    if s_me > s_opp then
      -- Current player ends with strictly larger score.
      .win
    else if s_opp > s_me then
      -- Opponent ends with strictly larger score.
      .loss
    else
      -- Scores are equal.
      .draw
  else
    -- Terminal rule / pruning:
    -- If even taking *all* remaining numbers would still leave the current player behind,
    -- then there is no legal catch-up sequence (in the TeX: no `$x_1,...,x_k$` with final sum ≥ gap).
    -- By the rules, the current player takes everything and the game ends immediately,
    -- but under this inequality they must still lose.
    if s_me + remaining.sum (fun x => x) < s_opp then
      .loss
    else
      -- Otherwise, the current player can pick some `$x \in$ remaining`.
      -- We evaluate every possible next pick under optimal play, then take the best outcome.
      let moves := remaining.attach.toList
      let outcomes := moves.map (fun ⟨x, _⟩ =>
        -- Take `x`: update current player's score and remove `x` from the set.
        let s_me' := s_me + x
        let remaining' := remaining.erase x

        if isFirstMove then
          -- First move rule (TeX item (1)):
          -- On the first move, `p1` must take exactly one element and then the turn passes.
          -- We therefore swap roles, evaluate from the opponent’s perspective, and negate
          -- to convert back to the current player's perspective.
          (valueAux remaining' s_opp s_me' false).neg
        else
          -- Subsequent move rule (TeX item (2)):
          -- On a turn, the current player must keep taking numbers while strictly behind,
          -- and stops as soon as they reach or exceed the opponent.
          if s_me' ≥ s_opp then
            -- We have caught up (or overtaken) on this pick: the turn ends and the opponent moves next.
            -- Swap players and negate to return to the current player's perspective.
            (valueAux remaining' s_opp s_me' false).neg
          else
            -- Still strictly behind after taking `x`: rules force us to continue the same turn,
            -- so the same player remains “current” in the recursive call.
            valueAux remaining' s_me' s_opp false
      )
      -- Optimal play: choose the best outcome among all legal next picks.
      .best outcomes
termination_by remaining.card
decreasing_by
  all_goals
    simpa [remaining'] using Finset.card_erase_lt_of_mem ‹_›

/-- Public API: The game-theoretic value of Catch-Up on the set `S`, assuming optimal play.
Returns `.win` if player 1 wins, `.loss` if player 2 wins, `.draw` if the game is tied. -/
noncomputable def value (S : Finset ℕ) : Outcome :=
  valueAux S 0 0 true

abbrev Target : Prop :=
    ∀ (N : ℕ) (h_even : Even (N * (N + 1) / 2)),
      value (.Icc 1 N) = .draw

end Problem
