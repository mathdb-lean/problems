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

- problem_id: E1046
- collection: erdos
- question_id: erdos:1046
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1046.lean#erdos_1046
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f\in \mathbb{C}[x]$ be a monic polynomial and $$E=\{ z: \lvert f(z)\rvert <1\}.$$ If $E$ is connected then is $E$ contained in a disc of radius $2$? A problem of Erdős, Herzog, and Piranian [EHP58], who also ask, if $\{ z: \lvert f(z)\rvert\leq 1\}$ is connected, then what are the least possible diameter and greatest possible width of this set, and conjecture the answer is $2$ in both cases. Their guess that the width is always at most $2$ is false, as Pommerenke [Po59] gave an example with width $>\sqrt{3}2^{1/3}\approx 2.18$. The condition that $E$ is connected is equivalent to $E$ containing all zeros of $f'$. The answer is yes, and in fact the centre of this disc can be taken to be $\frac{z_1+\cdots+z_n}{n}$, where the $z_i$ are the roots of $f$, as shown by Pommerenke [Po59].
- notes: Erdos Problem 1046 -- https://www.erdosproblems.com/1046
- track: solved
- answer_shape: decide
- source_stem: 1046
- mathdb_ref: erdos:1046
- source_namespace: Erdos1046
- source_theorem: erdos_1046
- source_category: research solved
- source_ams: 30
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Polynomial Metric

namespace Problem

/-- The open unit lemniscate $E = \{z : \lvert f(z)\rvert < 1\}$ of a complex polynomial. -/
def lemniscate (f : ℂ[X]) : Set ℂ := {z | ‖f.eval z‖ < 1}

/-- The closed unit lemniscate $\{z : \lvert f(z)\rvert \leq 1\}$ of a complex polynomial. -/
def closedLemniscate (f : ℂ[X]) : Set ℂ := {z | ‖f.eval z‖ ≤ 1}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ f : ℂ[X], f.Monic → IsConnected (lemniscate f) →
        ∃ c : ℂ, lemniscate f ⊆ ball c 2

end Problem
