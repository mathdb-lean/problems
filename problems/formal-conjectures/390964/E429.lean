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

- problem_id: E429
- collection: erdos
- question_id: erdos:429
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/429.lean#erdos_429
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that, if $A\subseteq \mathbb{N}$ is sparse enough and does not cover all residue classes modulo $p$ for any prime $p$, then there exists some $n\in \mathbb{Z}$ such that $n+a$ is prime for all $a\in A$? Weisenberg [We24] has shown the answer is no: $A$ can be arbitrarily sparse and missing at least one residue class modulo every prime $p$, and yet $A+n$ is not contained in the primes for any $n\in \mathbb{Z}$. (Weisenberg gives several constructions of such an $A$.)
- notes: Erdos Problem 429 -- https://www.erdosproblems.com/429
- track: solved
- answer_shape: decide
- source_stem: 429
- mathdb_ref: erdos:429
- source_namespace: Erdos429
- source_theorem: erdos_429
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
          ∀ A : Set ℕ, A.Infinite → (∀ N, (A ∩ Set.Icc 1 N).ncard ≤ f N) →
            (∀ p : ℕ, p.Prime → ∃ b : ZMod p, ∀ a ∈ A, (a : ZMod p) ≠ b) →
            ∃ n : ℤ, ∀ a ∈ A, (n + a).toNat.Prime

end Problem
