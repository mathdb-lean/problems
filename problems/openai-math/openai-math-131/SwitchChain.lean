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

- problem_id: SwitchChain
- collection: openai-math
- question_id: openai-math:131
- source: openai-math
- source_locator: lean/ComparatorChallenges/SwitchChain.lean#OAI.Problem315.switch_chain_main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves the simple-undirected Kannan–Tetali–Vempala conjecture: the lazy edge-switch chain mixes in $`O(n^8)`$ time for every graphical labeled degree sequence. The same degree-constrained graphs can also be sampled exactly uniformly by an almost-surely terminating algorithm with expected polynomial bit running time. ([Lean](lean/docs/131.md)) We prove the simple-undirected form of the Kannan–Tetali–Vempala conjecture: the switch chain on simple undirected graphs mixes in polynomial time for every graphical degree sequence. For a lazy chain that proposes switches uniformly on four vertices, the total-variation mixing time at distance 1/4 is at most $`2n^8`$. We also give an exactly uniform sampler for every graphical labeled degree vector. It uses unbiased random bits, terminates almost surely, and has expected polynomial bit running time.
- notes: OpenAI math result family 131, Rapid mixing of graph switches for every degree sequence -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/131.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Problem315.switch_chain_main OAI.Problem315.switch_chain_tv_bound OAI.Problem315.switch_connectivity
- source_theorem_count: 3
- source_solution_module: OAI.Probability.SwitchChain.Main
- source_papers: preprints/Polynomial-Mixing-of-the-Switch-Chain-for-Every-Graphical-Degree-Sequence-September-25-2026/main.pdf
- source_scope_note: lean/docs/131.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem315

def graphDegree {n : Nat} (G : SimpleGraph (Fin n)) (v : Fin n) : Nat := by
  classical
  exact (Finset.univ.filter (fun w => G.Adj v w)).card

def Realizes (n : Nat) (d : Fin n → Nat) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ v, graphDegree G v = d v

abbrev GraphState (n : Nat) (d : Fin n → Nat) :=
  {G : SimpleGraph (Fin n) // Realizes n d G}

def Graphical (n : Nat) (d : Fin n → Nat) : Prop :=
  Nonempty (GraphState n d)

abbrev FourSet (n : Nat) := {S : Finset (Fin n) // S.card = 4}

def IsPerfectMatchingOn {n : Nat} (S : Finset (Fin n))
    (M : SimpleGraph (Fin n)) : Prop :=
  ∀ v, (v ∈ S → ∃! w, M.Adj v w) ∧
    (v ∉ S → ∀ w, ¬ M.Adj v w)

abbrev PerfectMatching {n : Nat} (S : FourSet n) :=
  {M : SimpleGraph (Fin n) // IsPerfectMatchingOn S.1 M}

abbrev SwitchProposal (n : Nat) :=
  Σ S : FourSet n,
    {p : PerfectMatching S × PerfectMatching S // p.1 ≠ p.2}

def removedMatching {n : Nat} (p : SwitchProposal n) : SimpleGraph (Fin n) :=
  p.2.val.1.val

def addedMatching {n : Nat} (p : SwitchProposal n) : SimpleGraph (Fin n) :=
  p.2.val.2.val

def validSwitch {n : Nat} (G : SimpleGraph (Fin n))
    (p : SwitchProposal n) : Prop :=
  (∀ ⦃u v⦄, (removedMatching p).Adj u v → G.Adj u v) ∧
  (∀ ⦃u v⦄, (addedMatching p).Adj u v → ¬ G.Adj u v)

def replaceEdges {n : Nat} (G M N : SimpleGraph (Fin n)) :
    SimpleGraph (Fin n) where
  Adj u v := (G.Adj u v ∧ ¬ M.Adj u v) ∨ N.Adj u v
  symm := by
    constructor
    intro u v h
    rcases h with h | h
    · left
      exact ⟨G.symm.symm u v h.1, fun hm => h.2 (M.symm.symm v u hm)⟩
    · right
      exact N.symm.symm u v h
  loopless := by
    constructor
    intro v h
    rcases h with h | h
    · exact G.loopless.irrefl v h.1
    · exact N.loopless.irrefl v h

def proposalResult {n : Nat} (G : SimpleGraph (Fin n))
    (p : SwitchProposal n) : SimpleGraph (Fin n) := by
  classical
  exact
    if validSwitch G p then
      replaceEdges G (removedMatching p) (addedMatching p)
    else G

def allGraphStates (n : Nat) (d : Fin n → Nat) :
    Finset (GraphState n d) := by
  classical
  exact Finset.univ

def allProposals (n : Nat) : Finset (SwitchProposal n) := by
  classical
  exact Finset.univ

def stateCount (n : Nat) (d : Fin n → Nat) : Nat :=
  (allGraphStates n d).card

def switchKernel (n : Nat) (d : Fin n → Nat)
    (G H : GraphState n d) : ℝ := by
  classical
  exact
    (if G = H then (1 : ℝ) / 2 else 0) +
      (((allProposals n).filter
          (fun p => proposalResult G.val p = H.val)).card : ℝ) /
        (12 * (Nat.choose n 4 : ℝ))

def kernelPow (n : Nat) (d : Fin n → Nat) :
    Nat → GraphState n d → GraphState n d → ℝ := by
  classical
  intro t
  induction t with
  | zero =>
      exact fun G H => if G = H then 1 else 0
  | succ t previous =>
      exact fun G H =>
        Finset.sum (allGraphStates n d)
          (fun K => previous G K * switchKernel n d K H)

def uniformAverage (n : Nat) (d : Fin n → Nat)
    (f : GraphState n d → ℝ) : ℝ :=
  Finset.sum (allGraphStates n d) (fun G => f G) /
    (stateCount n d : ℝ)

def uniformInner (n : Nat) (d : Fin n → Nat)
    (f g : GraphState n d → ℝ) : ℝ :=
  uniformAverage n d (fun G => f G * g G)

def uniformVariance (n : Nat) (d : Fin n → Nat)
    (f : GraphState n d → ℝ) : ℝ :=
  uniformAverage n d
    (fun G => (f G - uniformAverage n d f) ^ 2)

def markovApply (n : Nat) (d : Fin n → Nat)
    (f : GraphState n d → ℝ) (G : GraphState n d) : ℝ :=
  Finset.sum (allGraphStates n d)
    (fun H => switchKernel n d G H * f H)

def dirichletEnergy (n : Nat) (d : Fin n → Nat)
    (f : GraphState n d → ℝ) : ℝ :=
  uniformInner n d f (fun G => f G - markovApply n d f G)

def hasSpectralGapAtLeast (n : Nat) (d : Fin n → Nat) (γ : ℝ) : Prop :=
  ∀ f : GraphState n d → ℝ,
    γ * uniformVariance n d f ≤ dirichletEnergy n d f

def tvDistanceFrom (n : Nat) (d : Fin n → Nat)
    (t : Nat) (G : GraphState n d) : ℝ :=
  (1 / 2 : ℝ) *
    Finset.sum (allGraphStates n d)
      (fun H =>
        |kernelPow n d t G H - (1 : ℝ) / (stateCount n d : ℝ)|)

def MixedAt (n : Nat) (d : Fin n → Nat) (t : Nat) : Prop :=
  ∀ G : GraphState n d, tvDistanceFrom n d t G ≤ (1 : ℝ) / 4

def mixingTime (n : Nat) (d : Fin n → Nat)
    (h : ∃ t : Nat, MixedAt n d t) : Nat := by
  classical
  exact Nat.find h

def SwitchStep (n : Nat) (d : Fin n → Nat)
    (G H : GraphState n d) : Prop :=
  ∃ p : SwitchProposal n,
    validSwitch G.val p ∧ proposalResult G.val p = H.val

def switch_chain_main_statement : Prop :=
  ∀ (n : Nat) (d : Fin n → Nat), 4 ≤ n → (∀ v, d v ≤ n - 1) → Graphical n d → ((∃ h : (∃ t : Nat, MixedAt n d t), mixingTime n d h ≤ 2 * n ^ 8) ∧ (stateCount n d = 1 → (MixedAt n d 0 ∧ ∀ h : (∃ t : Nat, MixedAt n d t), mixingTime n d h = 0)) ∧ (1 < stateCount n d → hasSpectralGapAtLeast n d ((1 : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ)))))

def switch_chain_tv_bound_statement : Prop :=
  ∀ (n : Nat) (d : Fin n → Nat), 4 ≤ n → (∀ v, d v ≤ n - 1) → Graphical n d → 1 < stateCount n d → ∀ (t : Nat) (G : GraphState n d), tvDistanceFrom n d t G ≤ Real.sqrt (stateCount n d : ℝ) / 2 * Real.exp (- (t : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ)))

def switch_connectivity_statement : Prop :=
  ∀ (n : Nat) (d : Fin n → Nat), 4 ≤ n → (∀ v, d v ≤ n - 1) → Graphical n d → ∀ G H : GraphState n d, Relation.ReflTransGen (SwitchStep n d) G H

end Problem315

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Problem315.switch_chain_main_statement ∧
  _root_.OAI.Problem315.switch_chain_tv_bound_statement ∧
  _root_.OAI.Problem315.switch_connectivity_statement

end Problem

/- Formalization scope, from lean/docs/131.md: The Kannan–Tetali–Vempala conjecture asks for polynomial mixing of the switch chain for every graphical degree sequence. The formalization proves the simple undirected case: for $n\ge4$, the lazy chain that proposes switches on four vertices has total-variation mixing time at distance $1/4$ at most $2n^8$. It also proves switch connectivity, the stated exponential total-variation bound, and a spectral gap of at least $1/(24n^2\binom n4)$ when more than one graph realizes the degree sequence. The paper's exactly uniform sampling algorithm is outside these selected chain estimates. -/
