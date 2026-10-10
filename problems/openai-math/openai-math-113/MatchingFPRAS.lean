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

- problem_id: MatchingFPRAS
- collection: openai-math
- question_id: openai-math:113
- source: openai-math
- source_locator: lean/ComparatorChallenges/MatchingFPRAS.lean#OAI.MatchingFPRAS.thm_main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Gives a fully polynomial randomized approximation scheme for counting perfect matchings in arbitrary finite simple graphs, with exact detection of zero counts. Also proves the perfect-matching entropy conjecture of Anari, Oveis Gharan, and Vinzant, bounding the maximum entropy of a matching law at every feasible edge-marginal vector in a loopless labelled multigraph, including boundary points. ([Lean](lean/docs/113.md)) We give a fully polynomial randomized approximation scheme (FPRAS) for counting perfect matchings in arbitrary finite simple undirected graphs, resolving the general-graph perfect-matching approximation problem. The algorithm returns zero with certainty when no perfect matching exists. Otherwise, it achieves relative error ε with failure probability at most δ in worst-case bit time polynomial in the input length, $`\varepsilon ^{-1}`$, and $`\log\delta^{-1}`$. We prove the perfect-matching entropy conjecture of Anari, Oveis Gharan, and Vinzant. For every feasible vector x of perfect-matching edge marginals in a loopless labelled multigraph on $`2m\ge2`$ vertices, the maximum entropy $`H(x)`$ of a matching law with marginals x satisfies
- notes: OpenAI math result family 113, Approximate counting and entropy of perfect matchings -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/113.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.MatchingFPRAS.thm_main
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.MatchingCount.Main
- source_papers: preprints/A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect-Matchings-in-General-Graphs-September-23-2026/main.pdf preprints/Entropy-and-Face-Dimension-of-the-Perfect-Matching-Polytope-September-23-2026/main.pdf
- source_scope_note: lean/docs/113.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace MatchingFPRAS

/-- Each unordered edge is represented once, by increasing endpoints. -/
structure GraphInput where
  n : ℕ
  edges : Finset (Fin n × Fin n)
  increasing : ∀ e ∈ edges, e.1 < e.2

/-- Exactly one selected edge is incident to every vertex. -/
def Perfect (G : GraphInput) (M : Finset (Fin G.n × Fin G.n)) : Prop :=
  M ⊆ G.edges ∧ ∀ v : Fin G.n, ∃! e, e ∈ M ∧ (e.1 = v ∨ e.2 = v)

noncomputable def perfectMatchings (G : GraphInput) : Finset (Finset (Fin G.n × Fin G.n)) :=
  by
    classical
    exact G.edges.powerset.filter (Perfect G)

/-- The exact unweighted count, including the empty graph. -/
noncomputable def Z (G : GraphInput) : ℕ := (perfectMatchings G).card

abbrev Symbol := Fin 8

/-- Binary numeral followed by a delimiter. Tape blank is 0; bits use 1 and 2. -/
def encodeNat (n : ℕ) : List Symbol :=
  (Nat.bits n).map (fun b => if b then 2 else 1) ++ [3]

def encodeInt (z : ℤ) : List Symbol :=
  (if z < 0 then [5] else [4]) ++ encodeNat z.natAbs

/-- A rational encoded by its reduced numerator and positive denominator. -/
def encodeRat (q : ℚ) : List Symbol := encodeInt q.num ++ encodeNat q.den

/-- Explicit sparse graph encoding, then the two rational parameters. -/
def encodeInput (G : GraphInput) (ε δ : ℚ) : List Symbol :=
  encodeNat G.n ++ encodeNat G.edges.card ++
    (((G.edges.map toLex.toEmbedding).sort (· ≤ ·)).flatMap fun e =>
      encodeNat (ofLex e).1.val ++ encodeNat (ofLex e).2.val) ++
    encodeRat ε ++ encodeRat δ

/-- A uniform randomized Post-Turing machine: a single finite transition table. -/
structure RandomMachine where
  states : ℕ
  transition : Fin (states + 1) → Symbol → Bool →
    Option (Fin (states + 1) × Turing.TM0.Stmt Symbol)

structure Configuration (A : RandomMachine) where
  state : Option (Fin (A.states + 1))
  tape : Turing.Tape Symbol

/-- A halted configuration is absorbing. Each nonhalting tick is exactly one
write or one move, or the detection of halt. -/
def tick (A : RandomMachine) (c : Configuration A) (bit : Bool) : Configuration A :=
  match c.state with
  | none => c
  | some s => match A.transition s c.tape.head bit with
    | none => ⟨none, c.tape⟩
    | some (s', action) =>
      ⟨some s', match action with
        | .move d => c.tape.move d
        | .write a => c.tape.write a⟩

def initial (A : RandomMachine) (input : List Symbol) : Configuration A :=
  ⟨some 0, Turing.Tape.mk₁ input⟩

/-- Bounded execution on a finite prefix of the random tape. -/
def run (A : RandomMachine) (input : List Symbol) {t : ℕ}
    (bits : Fin t → Bool) : Configuration A :=
  (List.ofFn bits).foldl (tick A) (initial A input)

def Outputs (A : RandomMachine) (input : List Symbol) {t : ℕ}
    (bits : Fin t → Bool) (q : ℚ) : Prop :=
  (run A input bits).state = none ∧
    (run A input bits).tape.right₀ = Turing.ListBlank.mk (encodeRat q)

/-- A fixed-degree polynomial in input bits, ε⁻¹, and log δ⁻¹.
Natural ceilings and binary ceiling-log change this bound only by constants. -/
def timeBound (C d : ℕ) (G : GraphInput) (ε δ : ℚ) : ℕ :=
  C * ((encodeInput G ε δ).length + ⌈ε⁻¹⌉₊ + Nat.clog 2 ⌈δ⁻¹⌉₊ + 1) ^ d

noncomputable def goodTapes (A : RandomMachine) (G : GraphInput) (ε δ : ℚ)
    (t : ℕ) : Finset (Fin t → Bool) := by
  classical
  exact Finset.univ.filter fun bits => ∃ q : ℚ,
    Outputs A (encodeInput G ε δ) bits q ∧
    (1 - ε) * (Z G : ℚ) ≤ q ∧ q ≤ (1 + ε) * (Z G : ℚ)

/-- A uniform approximation scheme using independent fair bits. All tapes halt
within the fixed polynomial bound and return a nonnegative rational.
A zero count always produces encoded zero. -/
def MainStatement : Prop :=
  ∃ (A : RandomMachine) (C d : ℕ), 0 < C ∧
    ∀ (G : GraphInput) (ε δ : ℚ), 0 < ε → ε < 1 → 0 < δ → δ < 1 / 2 →
      let t := timeBound C d G ε δ
      (∀ bits : Fin t → Bool, ∃ q : ℚ, 0 ≤ q ∧ Outputs A (encodeInput G ε δ) bits q) ∧
      (Z G = 0 → ∀ bits : Fin t → Bool, Outputs A (encodeInput G ε δ) bits 0) ∧
      ((goodTapes A G ε δ t).card : ℚ) / (2 : ℚ) ^ t ≥ 1 - δ


/-- A fully polynomial randomized approximation scheme for perfect matchings
in every finite simple undirected graph. -/
def thm_main_statement : Prop :=
  MainStatement

end MatchingFPRAS

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.MatchingFPRAS.thm_main_statement

end Problem

/- Formalization scope, from lean/docs/113.md: The formalization gives a fully polynomial randomized approximation scheme for counting perfect matchings in every finite simple undirected graph. For rational $0<\varepsilon<1$ and $0<\delta<1/2$, it returns a nonnegative rational estimate with relative error at most $\varepsilon$ with probability at least $1-\delta$. If the graph has no perfect matching, every execution returns zero. The algorithm is a fixed finite-alphabet randomized machine. Its worst-case running time is polynomial in the binary input length, $\varepsilon^{-1}$, and $\log(\delta^{-1})$, including on unsuccessful random tapes. For feasible edge marginals $x$ of perfect matchings in a loopless multigraph on $2m$ vertices, let $F(x)=-\sum_e x_e\log x_e$, $B(x)=-\sum_e(1-x_e)\log(1-x_e)$, and let $H(x)$ be the maximum entropy of a matching law with those marginals. The formalization proves $F(x)-(2-2/m)B(x)\le H(x)\le F(x)$ for $m\ge1$, including boundary points of the polytope. It retains the earlier coefficient-eight entropy bound and the deterministic counting approximations with factors $512^n$ for loopless graphs and $2^{18n}$ with singleton loops. A further statement identifies the exact face obtained by expanding a degree-three vertex into a triangle and shows that minimal faces are carried to minimal faces by the expansion. The paper's sharp global face-dimension bound is not part of that selected statement. -/
