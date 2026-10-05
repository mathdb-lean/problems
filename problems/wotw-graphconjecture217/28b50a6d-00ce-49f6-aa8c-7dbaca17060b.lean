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

- problem_id: WGraphConjecture217_conjecture217
- collection: wotw
- question_id: wotw:GraphConjecture217
- source: formal-conjectures
- source_locator: FormalConjectures/WrittenOnTheWallII/GraphConjecture217.lean#conjecture217
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: WOWII [Conjecture 217](http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj217): If $G$ is a finite simple connected graph on $n > 1$ vertices and $L_s(G) \le 4 \cdot \chi_{\mathrm{residue}=2}(G) + 2$, then $G$ has a Hamiltonian path. Here $L_s(G)$ is the maximum number of leaves over all spanning trees and $\chi_{\mathrm{residue}=2}(G)$ is the indicator of $\mathrm{residue}(G) = 2$.
- notes: Written on the Wall II, problem GraphConjecture217
- track: solved
- answer_shape: proof
- source_stem: GraphConjecture217
- source_namespace: WrittenOnTheWallII.GraphConjecture217
- source_theorem: conjecture217
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The **characteristic function** for the predicate $\mathrm{residue}\, G = 2$:
returns $1$ when $G.\mathrm{residue} = 2$ and $0$ otherwise. This is the WOWII
$\chi_{\mathrm{residue}=2}(G)$ indicator appearing in Conjecture 217. -/
noncomputable def residueEqTwoIndicator (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  if residue G = 2 then 1 else 0

abbrev Target : Prop :=
    ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
        (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2),
      ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

end Problem
