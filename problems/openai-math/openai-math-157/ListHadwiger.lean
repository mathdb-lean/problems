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

- problem_id: ListHadwiger
- collection: openai-math
- question_id: openai-math:157
- source: openai-math
- source_locator: lean/ComparatorChallenges/ListHadwiger.lean#OAI.LinearListHadwiger.main_theorem
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Disproves Hadwiger's conjecture even for fractional coloring: arbitrarily large finite simple graphs with independence number at most two satisfy $`\chi_f(G)\gt h(G)`$, where $`h(G)`$ is the largest clique-minor order. Also disproves the fractional Colin de Verdière chromatic bound $`\chi_f(G)\le\mu(G)+1`$. In the positive direction, every finite nonempty graph satisfies $`\chi_{\mathrm{list}}(G)\le C h(G)`$ for a universal constant C. ([Lean](lean/docs/157.md)) We prove that every finite nonempty graph G satisfies $`\chi_{\mathrm{list}}(G)\le C h(G)`$ for an absolute integer C, where $`h(G)`$ is the largest order of a clique minor. This resolves the Linear List Hadwiger conjecture affirmatively. We disprove Hadwiger's conjecture by constructing arbitrarily large graphs whose chromatic number exceeds their Hadwiger number. The examples have independence number at most two, and even their ordinary fractional chromatic number exceeds their Hadwiger number. Thus they also disprove the fractional-coloring weakening discussed by Reed and Seymour.
- notes: OpenAI math result family 157, Graph coloring, clique minors, and Colin de Verdière invariants -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/157.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.LinearListHadwiger.main_theorem
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.ListHadwiger.Main
- source_papers: preprints/A-linear-list-coloring-bound-in-terms-of-the-Hadwiger-number-September-23-2026/paper.pdf preprints/A-counterexample-to-Hadwigers-conjecture-September-23-2026/paper.pdf
- source_scope_note: lean/docs/157.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace LinearListHadwiger

def ListColorable {V : Type} (G : SimpleGraph V) {Color : Type}
    (L : V → Finset Color) : Prop :=
  ∃ c : V → Color, (∀ v, c v ∈ L v) ∧ ∀ ⦃v w⦄, G.Adj v w → c v ≠ c w

def Choosable {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (Color : Type) (L : V → Finset Color), (∀ v, k ≤ (L v).card) → ListColorable G L

noncomputable def listChromaticNumber {V : Type} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | Choosable G k}

def HasCliqueMinor {V : Type} (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ B : Fin t → Set V,
    (∀ i, (G.induce (B i)).Connected) ∧
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
    (∀ i j, i ≠ j → ∃ v ∈ B i, ∃ w ∈ B j, G.Adj v w)

noncomputable def hadwigerNumber {V : Type} (G : SimpleGraph V) : ℕ :=
  sSup {t : ℕ | HasCliqueMinor G t}

def MainStatement : Prop :=
  ∃ C : ℕ, 1 ≤ C ∧ ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V),
    listChromaticNumber G ≤ C * hadwigerNumber G

def main_theorem_statement : Prop :=
  MainStatement

end LinearListHadwiger

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.LinearListHadwiger.main_theorem_statement

end Problem

/- Formalization scope, from lean/docs/157.md: Hadwiger's conjecture predicts $\chi(G)\le h(G)$ for every finite graph, where $h(G)$ is the largest clique-minor order. The formalization constructs arbitrarily large finite simple counterexamples with independence number at most two. For a graph on $m$ vertices it proves $h(G)<26m/75+2/3<m/2\le\chi(G)$. This disproves the ordinary chromatic form. The paper's fractional-chromatic strengthening and the Colin de Verdière consequence are outside this selected statement. The Linear List Hadwiger conjecture asks for a universal linear bound on list chromatic number in terms of clique-minor size. The formalization proves that there is one integer $C\ge1$ such that every finite nonempty simple graph $G$ satisfies $\chi_{\mathrm{list}}(G)\le C h(G)$, where $h(G)$ is the largest order of a clique minor. The constant is independent of the graph. -/
