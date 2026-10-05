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

- problem_id: E486
- collection: erdos
- question_id: erdos:486
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/486.lean#erdos_486
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A \subseteq \mathbb{N}$, and for each $n \in A$ choose some $X_n \subseteq \mathbb{Z}/n\mathbb{Z}$. Let $B = \{m \in \mathbb{N} : m \not\in X_n \pmod{n} \text{ for all } n \in A \text{ with } m > n\}$. Must $B$ have a logarithmic density? The set $A$ is encoded by taking $X_n = \emptyset$ for $n \notin A$. Only positive moduli $n$ are considered, since $\mathbb{Z}/0\mathbb{Z} = \mathbb{Z}$ would allow $B$ to be an arbitrary set. The answer is no: Wang [Wa26] (with GPT-5.6) constructed a congruence system whose survivor set $B$ has lower logarithmic density at most $177/200$ and upper logarithmic density at least $49/50$. The first linked formal proof establishes this for the real-cutoff normalisation $\frac{1}{\log x}\sum_{m < x, m \in B} \frac{1}{m}$ with the moduli restricted to $A$; the second derives the statement below (`Set.HasLogDensity`, all moduli) from it.
- notes: Erdos Problem 486 -- https://www.erdosproblems.com/486
- track: solved
- answer_shape: decide
- source_stem: 486
- mathdb_ref: erdos:486
- source_namespace: Erdos486
- source_theorem: erdos_486
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ X : (n : ℕ) → Set (ZMod n),
          ∃ d, {m : ℕ | ∀ n, 0 < n → n < m → (m : ZMod n) ∉ X n}.HasLogDensity d

end Problem
