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

- problem_id: E516
- collection: erdos
- question_id: erdos:516
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/516.lean#erdos_516
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let `f = ∑ aₖzⁿₖ` be an entire function of finite order such that `nₖ / k → ∞`. Then `limsup (fun r => ratio r f) atTop = 1`. This is proved in [Fu63].
- notes: Erdos Problem 516 -- https://www.erdosproblems.com/516
- track: solved
- answer_shape: proof
- source_stem: 516
- mathdb_ref: erdos:516
- source_namespace: Erdos516
- source_theorem: erdos_516
- source_category: research solved
- source_ams: 30
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open scoped Nat
open Filter Real Set

namespace Problem

/-- An entire function `f` is said to be of finite order if there exist numbers c, a ≥ 0
such that for all `z`, `‖f z‖ ≤ c * rexp (‖z‖ ^ a)`. -/
def OfFiniteOrder {E F: Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (f : E → F) : Prop :=
  Differentiable ℂ f ∧ ∃ c ≥ 0, ∃ a ≥ 0, ∀ z, ‖f z‖ ≤ c * rexp (‖z‖ ^ a)

noncomputable def ratio (r : ℝ) (f : ℂ → ℂ) : ℝ :=
  (⨅ z : {z : ℂ // ‖z‖ = r}, ‖f z‖).log / (⨆ z : {z : ℂ // ‖z‖ = r}, ‖f z‖).log

abbrev Target : Prop :=
    ∀ {f : ℂ → ℂ} {n : ℕ → ℕ}
        (hn : HasFabryGaps n) {a : ℕ → ℂ} (ha : ∀ n, a n ≠ 0)
        (hfn : ∀ z, HasSum (fun k => a k * z ^ n k) (f z)) (hf : OfFiniteOrder f),
      limsup (fun r => ratio r f) atTop = 1

end Problem
