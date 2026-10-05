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

- problem_id: X0912_2382_CurlingNumberConjecture_curling_number_conjecture
- collection: arxiv
- question_id: arxiv:0912.2382/CurlingNumberConjecture
- source: formal-conjectures
- source_locator: FormalConjectures/Arxiv/0912.2382/CurlingNumberConjecture.lean#curling_number_conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: The sequence will eventually reach $1$.
- notes: arXiv 0912.2382/CurlingNumberConjecture -- https://arxiv.org/abs/0912.2382
- track: open
- answer_shape: proof
- source_stem: 0912.2382/CurlingNumberConjecture
- source_namespace: Arxiv.«0912.2382»
- source_theorem: curling_number_conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
The curling number

Let $S$ be a finite nonempty sequence of integers. By grouping adjacent terms, it is always possible
to write it as $S = X Y Y . . . Y = X Y^k$, where $X$ and $Y$ are sequences of integers and $Y$ is nonempty
($X$ is allowed to be the empty sequence $∅$). There may be several ways to do this: choose the one
that maximizes the value of $k$: this $k$ is the curling number of $S$, denoted by $k S$.
-/
noncomputable def k (S : List ℤ) : ℕ :=
  sSup {k : ℕ | ∃ X Y : List ℤ, Y ≠ [] ∧ S = X ++ (List.replicate k Y).flatten}

/--
One starts with any initial
sequence of integers $S₀$, and extends it by repeatedly appending the curling number of the current
sequence.
-/
noncomputable def S (S₀ : List ℤ) (n : ℕ) : List ℤ :=
  match n with
  | 0 => S₀
  | n + 1 => (S S₀ n) ++ [Int.ofNat (k (S S₀ n))]

abbrev Target : Prop :=
    ∀ (S₀ : List ℤ) (h : S₀ ≠ []),
      ∃ m, k (S S₀ m) = 1

end Problem
