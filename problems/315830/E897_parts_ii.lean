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

- problem_id: E897_parts_ii
- collection: erdos
- question_id: erdos:897
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/897.lean#erdos_897.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f(n)$ be an additive function (so that $f(ab)=f(a)+f(b)$ if $(a,b)=1$) such that $\limsup_{p,k} f(p^k) / \log(p^k) = ∞$. Is it true that $\limsup_n f(n+1)/ f(n) = ∞$? The answer is no; the same counterexample is formalised in Lean by Aristotle [ArWu25].
- notes: Erdos Problem 897 -- https://www.erdosproblems.com/897
- track: solved
- answer_shape: decide
- source_stem: 897
- mathdb_ref: erdos:897
- source_namespace: Erdos897
- source_theorem: erdos_897.parts.ii
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

-- TODO(lezeau): add `ArithmeticFunction.IsAdditive` to `ForMathlib`

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ (f : ℕ → ℝ),
        (∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b) →
        ((Filter.atTop ⊓ Filter.principal {(p, k) : ℕ × ℕ | p.Prime}).limsup
          (fun (p, k) => (f (p^k) / (p^k : ℝ).log : EReal)) = ⊤) →
        Filter.atTop.limsup (fun (n : ℕ) => (f (n+1) / f n : EReal)) = ⊤

end Problem
