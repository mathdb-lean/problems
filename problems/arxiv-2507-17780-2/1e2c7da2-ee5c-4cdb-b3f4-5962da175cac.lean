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

- problem_id: X2507_17780_2_tx_graffiti_conjecture_2
- collection: arxiv
- question_id: arxiv:2507.17780/2
- source: formal-conjectures
- source_locator: FormalConjectures/Arxiv/2507.17780/2.lean#tx_graffiti_conjecture_2
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: TxGraffiti [Conjecture 2](https://arxiv.org/abs/2507.17780): for every connected graph $G$ with $\Delta(G) \le 3$ and $G \ne K_4$, $$Z(G) \le \alpha(G) + 1.$$ This conjecture is **open**.
- notes: arXiv 2507.17780/2 -- https://arxiv.org/abs/2507.17780
- track: open
- answer_shape: proof
- source_stem: 2507.17780/2
- source_namespace: Arxiv.«2507.17780»
- source_theorem: tx_graffiti_conjecture_2
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open SimpleGraph

namespace Problem

/-- One step of the zero forcing colour-change rule: add to $S$ every vertex $w$
that is the unique neighbour of some $v \in S$ outside $S$. -/
noncomputable def zeroForcingStep {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  S ∪ Finset.univ.filter fun w =>
    w ∉ S ∧ ∃ v ∈ S, G.Adj v w ∧ ∀ u, G.Adj v u → u ∉ S → u = w

/-- The zero forcing closure: iterate `zeroForcingStep` until it stabilises. -/
noncomputable def zeroForcingClosure {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  (zeroForcingStep G)^[Fintype.card V] S

/-- A set $S$ is a *zero forcing set* of $G$ if its zero forcing closure is all
of $V$. -/
def IsZeroForcingSet {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Prop :=
  zeroForcingClosure G S = Finset.univ

/-- The zero forcing number of a finite simple graph: the minimum cardinality of
a zero forcing set. -/
noncomputable def zeroForcingNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {k | ∃ S : Finset V, S.card = k ∧ IsZeroForcingSet G S}

abbrev Target : Prop :=
    ∀ (V : Type) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected)
        (_hDeg : G.maxDegree ≤ 3) (_hNotK4 : G = ⊤ → Fintype.card V ≠ 4),
      zeroForcingNumber G ≤ G.indepNum + 1

end Problem
