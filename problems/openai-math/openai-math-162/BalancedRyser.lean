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

- problem_id: BalancedRyser
- collection: openai-math
- question_id: openai-math:162
- source: openai-math
- source_locator: lean/ComparatorChallenges/BalancedRyser.lean#OAI.Balanced.main_result
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Disproves Ryser's covering conjecture by constructing intersecting $`(q+1)`$-partite, $`(q+1)`$-uniform hypergraphs with covering number $`q+1`$, rather than the predicted bound q, for every sufficiently large prime q. A separate construction over extension fields also disproves Gyárfás's monochromatic tree-cover conjecture. ([Lean](lean/docs/162.md)) For every sufficiently large prime q, we construct a finite intersecting $`(q+1)`$-partite $`(q+1)`$-uniform hypergraph with covering number $`q+1`$ and exactly $`q+1`$ nonisolated vertices in each part. This disproves Ryser's covering conjecture, even for intersecting hypergraphs with equally sized parts. For every sufficiently large prime $`s\equiv2\pmod3`$ and every sufficiently large odd integer n, with the threshold depending on s, we construct an intersecting $`(s^n+1)`$-partite $`(s^n+1)`$-uniform hypergraph with covering number $`s^n+1`$. This disproves Ryser's covering conjecture in its intersecting case.
- notes: OpenAI math result family 162, Counterexamples to Ryser’s covering conjecture -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/162.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Balanced.main_result
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.BalancedRyser.Main
- source_papers: preprints/Balanced-Counterexamples-to-Rysers-Conjecture-at-Prime-Orders-September-27-2026/paper.pdf preprints/A-Counterexample-to-Rysers-Covering-Conjecture-September-23-2026/paper.pdf
- source_scope_note: lean/docs/162.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace Balanced
open scoped _root_.Balanced

structure PartiteHypergraph (r n : ℕ) where
  edges : Finset (Fin r → Fin n)

namespace PartiteHypergraph

variable {r n : ℕ}

abbrev Vertex (r n : ℕ) := Fin r × Fin n

def Covers (H : PartiteHypergraph r n) (C : Finset (Vertex r n)) : Prop :=
  ∀ e ∈ H.edges, ∃ i, (i, e i) ∈ C

def Intersecting (H : PartiteHypergraph r n) : Prop :=
  H.edges.Nonempty ∧ ∀ e ∈ H.edges, ∀ f ∈ H.edges, ∃ i, e i = f i

def Nonisolated (H : PartiteHypergraph r n) : Prop :=
  ∀ i v, ∃ e ∈ H.edges, e i = v

def HasCoverNumber (H : PartiteHypergraph r n) (k : ℕ) : Prop :=
  (∃ C : Finset (Vertex r n), H.Covers C ∧ C.card = k) ∧
    ∀ C : Finset (Vertex r n), H.Covers C → k ≤ C.card

end PartiteHypergraph

def BalancedCounterexample (q : ℕ) : Prop :=
  ∃ H : PartiteHypergraph (q + 1) (q + 1),
    H.Intersecting ∧ H.Nonisolated ∧ H.HasCoverNumber (q + 1)

def MainResult : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → q.Prime → BalancedCounterexample q

def main_result_statement : Prop :=
  MainResult

end Balanced

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Balanced.main_result_statement

end Problem

/- Formalization scope, from lean/docs/162.md: Ryser's covering conjecture predicts that an intersecting $r$-partite hypergraph has a vertex cover of size at most $r-1$. The formalization proves that every sufficiently large prime $q$ has a finite intersecting $(q+1)$-partite, $(q+1)$-uniform hypergraph with covering number $q+1$ and exactly $q+1$ nonisolated vertices in each part. Thus the conjecture fails even with equal part sizes. The prime threshold is existential. Ryser's covering conjecture predicts $\tau\le(r-1)\nu$ for an $r$-partite hypergraph, where $\tau$ and $\nu$ are its covering and matching numbers. The formalized constructions give finite intersecting $r$-partite $r$-uniform hypergraphs with $\nu=1$ and $\tau=r$, contradicting the bound. The ranks have the form $r=p^n+1$: one fixed prime $p\equiv2\pmod3$ works for all sufficiently large prime degrees $n$, and a second result covers every sufficiently large such prime $p$ and every sufficiently large odd $n$, with the degree threshold allowed to depend on $p$. Infinitely many ranks occur. Equal part sizes and numerical thresholds are not asserted. -/
