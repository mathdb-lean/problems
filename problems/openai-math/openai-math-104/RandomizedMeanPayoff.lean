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

- problem_id: RandomizedMeanPayoff
- collection: openai-math
- question_id: openai-math:104
- source: openai-math
- source_locator: lean/ComparatorChallenges/RandomizedMeanPayoff.lean#OAI.randomized_quasipolynomial_mean_payoff
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Gives deterministic algorithms using $`2^{O((\log(L+2))^2)}`$ bit operations, for complete binary input length L, for ordinary mean-payoff games and two separate extensions. They compute exact values and optimal positional strategies in ordinary games, the nonnegative expectation-of-liminf value set in turn-based stochastic games, and the winning set for nonnegative liminf mean payoff conjoined with parity. Signed rewards, rational chance probabilities, and parity priorities are unrestricted and binary-encoded. ([Lean](lean/docs/104.md)) We give a deterministic algorithm that computes the complete zero-threshold winning set of a finite mean-payoff game with arbitrary signed integer edge weights encoded in binary. For total explicit input length L, it uses $`2^{O((\log(L+2))^2)}`$ bit operations. A reduction also computes the exact rational value at every vertex and globally optimal positional strategies for both players within the same quasipolynomial bound. We give a randomized algorithm that computes the complete zero-threshold winning set of a finite mean-payoff game with arbitrary signed integer edge weights encoded in binary. For total explicit input length L, it uses $`2^{O((\log(L+2))^2)}`$ bit operations on every random tape and is correct with probability at least 7/8. A polynomial-time check certifies the winning regions and positional strategies for both players or reports failure. Independent repetition therefore gives an always-correct algorithm with the same expected quasipolynomial bit bound.
- notes: OpenAI math result family 104, Quasipolynomial algorithms for mean-payoff, stochastic and parity games -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/104.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.randomized_quasipolynomial_mean_payoff
- source_theorem_count: 1
- source_solution_module: OAI.Computability.RandomMean.Main
- source_main_result: OAI.randomized_quasipolynomial_mean_payoff
- source_papers: preprints/Deterministic-quasipolynomial-time-mean-payoff-games-September-25-2026/paper.pdf preprints/Randomized-quasipolynomial-time-mean-payoff-games-September-25-2026/paper.pdf
- source_scope_note: lean/docs/104.md
- source_field: Computability
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace MeanPayoff
structure Game where
  n : ℕ
  positive : 0 < n
  m : ℕ
  tail : Fin m → Fin n
  head : Fin m → Fin n
  maxOwner : Fin n → Bool
  weight : Fin m → ℤ
  total : ∀ v : Fin n, ∃ e : Fin m, tail e = v

def Strategy (G : Game) :=
  List (Fin G.m) → (v : Fin G.n) → {e : Fin G.m // G.tail e = v}

def move (G : Game) (σ τ : Strategy G) (v : Fin G.n)
    (history : List (Fin G.m)) : Fin G.m :=
  if G.maxOwner v then (σ history v).val else (τ history v).val

def position (G : Game) (σ τ : Strategy G) (start : Fin G.n) :
    ℕ → Fin G.n × List (Fin G.m)
  | 0 => (start, [])
  | t + 1 =>
    let p := position G σ τ start t
    let e := move G σ τ p.1 p.2
    (G.head e, p.2 ++ [e])

def play (G : Game) (σ τ : Strategy G) (start : Fin G.n) (t : ℕ) : Fin G.m :=
  let p := position G σ τ start t
  move G σ τ p.1 p.2

noncomputable def meanPayoff (G : Game) (π : ℕ → Fin G.m) : ℝ :=
  Filter.liminf (fun T : ℕ =>
    (∑ j ∈ Finset.range T, (G.weight (π j) : ℝ)) / (T : ℝ)) Filter.atTop

def Winning (G : Game) (v : Fin G.n) : Prop :=
  ∃ σ : Strategy G, ∀ τ : Strategy G, 0 ≤ meanPayoff G (play G σ τ v)

def encodeNat (n : ℕ) : List Bool :=
  let bits := Nat.bits (n + 1)
  List.replicate bits.length true ++ [false] ++ bits

def encodeInt (z : ℤ) : List Bool :=
  decide (z < 0) :: encodeNat z.natAbs

def input (G : Game) : List Bool :=
  encodeNat G.n ++ encodeNat G.m ++ List.ofFn G.maxOwner ++
    (List.ofFn (fun e : Fin G.m =>
      encodeNat ((G.tail e).val + 1) ++ encodeNat ((G.head e).val + 1) ++
        encodeInt (G.weight e))).flatten

abbrev Symbol := Option Bool

inductive Direction where
  | left | stay | right
  deriving DecidableEq

def Direction.offset : Direction → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

structure Action (q : ℕ) where
  next : Fin q
  write : Fin 3 → Symbol
  shift : Fin 3 → Direction

structure Machine where
  states : ℕ
  start : Fin states
  transition : Fin states → (Fin 3 → Symbol) → Bool → Option (Action states)

structure Configuration (M : Machine) where
  control : Option (Fin M.states)
  head : Fin 3 → ℤ
  tape : Fin 3 → ℤ → Symbol

def initial (M : Machine) (code : List Bool) : Configuration M where
  control := some M.start
  head := fun _ => 0
  tape := fun k j => if k = 0 ∧ 0 ≤ j then code[j.toNat]? else none

def step (M : Machine) (c : Configuration M) (bit : Bool) : Configuration M :=
  match c.control with
  | none => c
  | some s =>
    match M.transition s (fun k => c.tape k (c.head k)) bit with
    | none => { c with control := none }
    | some a =>
      { control := some a.next
        head := fun k => c.head k + (a.shift k).offset
        tape := fun k => Function.update (c.tape k) (c.head k) (a.write k) }

def run (M : Machine) (code : List Bool) (random : ℕ → Bool) : ℕ → Configuration M
  | 0 => initial M code
  | t + 1 => step M (run M code random t) (random t)

def padBits {T : ℕ} (bits : Fin T → Bool) (j : ℕ) : Bool :=
  if h : j < T then bits ⟨j, h⟩ else false

def result (M : Machine) (G : Game) (T : ℕ) (bits : Fin T → Bool) : Configuration M :=
  run M (input G) (padBits bits) T

def CorrectOutput (G : Game) {M : Machine} (c : Configuration M) : Prop :=
  c.control = none ∧
  (∀ v : Fin G.n, c.tape 2 (v.val : ℤ) = some true ↔ Winning G v) ∧
  (∀ v : Fin G.n, c.tape 2 (v.val : ℤ) = some false ↔ ¬ Winning G v) ∧
  ∀ j : ℤ, (j < 0 ∨ (G.n : ℤ) ≤ j) → c.tape 2 j = none

noncomputable def MainClaim : Prop := by
  classical
  exact ∃ M : Machine, ∃ C : ℝ, 0 < C ∧ ∀ G : Game, ∃ T : ℕ,
    (T : ℝ) ≤ (2 : ℝ) ^ (C * (Real.logb 2 ((input G).length + 2)) ^ 2) ∧
    (∀ bits : Fin T → Bool, (result M G T bits).control = none) ∧
    7 * 2 ^ T ≤ 8 * (Finset.univ.filter
      (fun bits : Fin T → Bool => CorrectOutput G (result M G T bits))).card

end MeanPayoff

def randomized_quasipolynomial_mean_payoff_statement : Prop :=
  MeanPayoff.MainClaim

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.randomized_quasipolynomial_mean_payoff_statement

end Problem

/- Formalization scope, from lean/docs/104.md: The formalization checks that a specified two-step execution of Truffet's elimination procedure terminates with a feasible but nonoptimal output. It is a finite counterexample to that proposed optimization step. The formalized result gives one randomized algorithm for the complete zero-threshold winning set of every finite mean-payoff game with signed binary weights. It succeeds with probability at least $7/8$ and runs in quasipolynomial bit time on every random tape. Self-loops, parallel edges, and history-dependent strategies are allowed, and winning means a nonnegative liminf average payoff. -/
