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

import MathDBUtil

/-!
Converted from another corpus. `source` names it, `source_version`
pins the revision, and `source_locator` points at the one
declaration this came from. Every `source_` field describes that
declaration as it stands there, not as it stands here.

Read `track` for whether the problem is solved, which is a fact
about mathematics. `source_has_lean_proof` is a different claim --
whether that corpus holds a machine-checked proof -- and is false
for almost every problem, because it is a statement repository.

- problem_id: E848
- collection: erdos
- question_id: erdos:848
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/848.lean#erdos_848
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is the maximum size of a set $A ⊆ \{1, \dots, N\}$ such that $ab + 1$ is never squarefree (for all $a, b ∈ A$) achieved by taking those $n ≡ 7 \pmod{25}$? This asks whether `Erdos848 N` holds for all $N$ (formulated using `A ⊆ Finset.range N`). This was solved for all sufficiently large $N$ by Sawhney in this note. In fact, Sawhney proves something slightly stronger, that there exists some constant $c>0$ such that if $\lvert A\rvert \geq (\frac{1}{25}-c)N$ and $N$ is large then $A$ is contained in either $\{ n\equiv 7\pmod{25}\}$ or $\{n\equiv 18\pmod{25}\}$.
- notes: Erdos Problem 848 -- https://www.erdosproblems.com/848
- track: solved
- answer_shape: decide
- source_stem: 848
- mathdb_ref: erdos:848
- source_namespace: Erdos848
- source_theorem: erdos_848
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

/-- A set $A$ has the non-squarefree product property if $ab + 1$ is not squarefree
for all $a, b ∈ A$. -/
def NonSquarefreeProductProp (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ¬Squarefree (a * b + 1)

/-- The candidate extremal set: $\{n ∈ \{0, \dots, N-1\} : n ≡ 7 (mod 25)\}$. -/
def A₇ (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun n => n % 25 = 7)

/-- The Erdős Problem 848 statement for a fixed $N$: any set $A ⊆ \{0, \dots, N-1\}$ with
the non-squarefree product property has cardinality at most $|A₇(N)|$. -/
def Erdos848For (N : ℕ) : Prop :=
  ∀ A : Finset ℕ, A ⊆ Finset.range N → NonSquarefreeProductProp A →
    A.card ≤ (A₇ N).card

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ N, Erdos848For N

end Problem
