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

- problem_id: E1146_refute
- collection: erdos
- question_id: erdos:1146
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1146.lean#erdos_1146
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is $B=\{2^m3^n : m,n\geq 0\}$ an essential component? In [Ru99] Ruzsa states "The simplest set with a chance to be an essential component is the collection of numbers in the form $2^m3^n$ and Erdős often asked whether it is an essential component or not; I do not even have a plausible guess."
- notes: Erdos Problem 1146 -- https://www.erdosproblems.com/1146
- track: open
- answer_shape: refute
- pair_id: E1146
- pair_role: refute
- source_stem: 1146
- mathdb_ref: erdos:1146
- source_namespace: Erdos1146
- source_theorem: erdos_1146
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open scoped Pointwise

namespace Problem

/--
We say that $A\subset \mathbb{N}$ is an essential component if $d_s(A \oplus B)>d_s(B)$ for every
$B\subset \mathbb{N}$ with $0<d_s(B)<1$ where $d_s$ is the Schnirelmann density.
Here, the sumset is the appropriate one for Schnirelmann density, $A \oplus B = \{a+b \mid a \in A \cup \{0\}, b \in B \cup \{0\}\}$ (i.e. $(A \cup \{0\}) + (B \cup \{0\})$).
This avoids the trivial case where the sumset misses $1$ simply because neither $A$ nor $B$ contains $0$.
-/
def IsEssentialComponent (A : Set ℕ) : Prop :=
  open scoped Classical in
  ∀ B : Set ℕ,
    let b := schnirelmannDensity B;
    0 < b → b < 1 → schnirelmannDensity ((A ∪ {0}) + (B ∪ {0})) > b

abbrev Target : Prop :=
    ¬ (
      IsEssentialComponent { k | ∃ m n : ℕ, k = 2 ^ m * 3 ^ n }
    )

end Problem
