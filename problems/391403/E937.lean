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

- problem_id: E937
- collection: erdos
- question_id: erdos:937
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/937.lean#erdos_937
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Are there infinitely many four-term arithmetic progressions of coprime powerful numbers? (A number $n$ is *powerful* if $p \mid n \to p^2 \mid n$; `Nat.Powerful`.) Erdős [Er76d] asked this; the answer is **yes**: Bajpai, Bennett and Chan [BBC24] proved that there are infinitely many four-term arithmetic progressions of pairwise coprime powerful numbers. (Without coprimality this is easy, and by a theorem of Fermat there are no four *squares* in arithmetic progression.)
- notes: Erdos Problem 937 -- https://www.erdosproblems.com/937
- track: solved
- answer_shape: decide
- source_stem: 937
- mathdb_ref: erdos:937
- source_namespace: Erdos937
- source_theorem: erdos_937
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: not_isCoprimePowerfulAP4_zero_one
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

open Nat

/-- The four numbers $a, a+d, a+2d, a+3d$ form a four-term arithmetic progression ($d > 0$) of
pairwise coprime powerful numbers. -/
def IsCoprimePowerfulAP4 (a d : ℕ) : Prop :=
  0 < d ∧
  a.Powerful ∧ (a + d).Powerful ∧ (a + 2 * d).Powerful ∧ (a + 3 * d).Powerful ∧
  a.Coprime (a + d) ∧ a.Coprime (a + 2 * d) ∧ a.Coprime (a + 3 * d) ∧
  (a + d).Coprime (a + 2 * d) ∧ (a + d).Coprime (a + 3 * d) ∧ (a + 2 * d).Coprime (a + 3 * d)

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Sanity check for `IsCoprimePowerfulAP4`: the progression $0, 1, 2, 3$ is not a valid
example, since $2$ is not powerful. -/
@[category test, AMS 11]
theorem not_isCoprimePowerfulAP4_zero_one : ¬ IsCoprimePowerfulAP4 0 1 := by
  intro h
  obtain ⟨-, -, -, h2, -⟩ := h
  exact Nat.not_full_of_prime_mod_prime_sq 2 1 Nat.prime_two (by norm_num) h2

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ {p : ℕ × ℕ | IsCoprimePowerfulAP4 p.1 p.2}.Infinite

end Problem
