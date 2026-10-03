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

- problem_id: E1064
- collection: erdos
- question_id: erdos:1064
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1064.lean#erdos_1064
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $ϕ(n)$ be the Euler's totient function, then the $n$ satisfies $ϕ(n)>ϕ(n - ϕ(n))$ have asymptotic density 1. Reference: [LuPo02] Luca, Florian and Pomerance, Carl, On some problems of {M}\polhk akowski-{S}chinzel and {E}rd\H os concerning the arithmetical functions {$\phi$} and {$\sigma$}. Colloq. Math.
- notes: Erdos Problem 1064 -- https://www.erdosproblems.com/1064
- track: solved
- answer_shape: proof
- source_stem: 1064
- mathdb_ref: erdos:1064
- source_namespace: Erdos1064
- source_theorem: erdos_1064
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Nat Filter Topology

namespace Problem

open Asymptotics Filter

abbrev Target : Prop :=
    {n | φ n > φ (n - φ n)}.HasDensity 1

end Problem
