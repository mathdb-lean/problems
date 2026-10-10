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

- problem_id: O237271_conjecture_2
- collection: oeis
- question_id: oeis:237271
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/237271.lean#conjecture_2
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture 2: "a(n) is the number of 2-dense sublists of divisors of n. We call '2-dense sublists of divisors of n' to the maximal sublists of divisors of n whose terms increase by a factor of at most 2." - _Omar E. Pol_, Jul 31 2025 A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
- notes: OEIS A237271 -- https://oeis.org/A237271
- track: solved
- answer_shape: proof
- source_stem: 237271
- source_namespace: OeisA237271
- source_theorem: conjecture_2
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Nat Finset List

/--
Number of parts in the symmetric representation of $\sigma(n)$. $a(n)$ is $1$ plus the number of pairs $(d_k, d_{k+1})$ of consecutive divisors of $n$
such that $d_{k+1}$ is odd and $d_{k+1} \ge 2 d_k$.

The formula used is
$1 + |\{(d_k, d_{k+1}) \in \text{consecutive pairs of divisors of } n \mid
d_{k+1} \text{ is odd and } d_{k+1} \ge 2 d_k\}|$,
which is a known characterization of the sequence.
-/
def a (n : ℕ) : ℕ :=
  -- Get the list of divisors of n, sorted ascendingly.
  let divs_list : List ℕ := (n.divisors.sort (· ≤ ·))

  -- Get the list of consecutive pairs of divisors: [(d₁, d₂), (d₂, d₃), ...]
  let consecutive_pairs : List (ℕ × ℕ) := List.zip divs_list divs_list.tail

  -- Count the pairs satisfying the condition
  let count : ℕ := consecutive_pairs.countP fun pair =>
    let d_k := pair.fst
    let d_k_succ := pair.snd
    -- The second divisor d_{k+1} must be odd and at least twice the first divisor d_k.
    Odd d_k_succ ∧ d_k_succ ≥ 2 * d_k

  -- The sequence value is 1 + the count
  1 + count

def sortedDivisorsList (n : ℕ) : List ℕ := (n.divisors.sort (· ≤ ·))

/--
Number of maximal contiguous sublists of divisors of n where each adjacent pair (d_k, d_{k+1})
satisfies d_{k+1} <= 2 * d_k.
This is 1 + the number of "jumps" where d_{k+1} > 2 * d_k.
-/
def num2DenseSublists (n : ℕ) : ℕ :=
  let divs_list := sortedDivisorsList n
  let consecutive_pairs : List (ℕ × ℕ) := List.zip divs_list divs_list.tail

  -- A jump/break occurs when d_{k+1} > 2 * d_k
  let num_jumps : ℕ := consecutive_pairs.countP fun pair =>
    let d_k := pair.fst
    let d_k_succ := pair.snd
    d_k_succ > 2 * d_k

  1 + num_jumps

/-- Number of odd divisors of n (A001227). -/
def A001227 (n : ℕ) : ℕ := (n.divisors.filter Odd).card

/-- Number of odd divisors m of n such that there is a divisor d of n with d < m < 2*d (A239657). -/
def A239657 (n : ℕ) : ℕ :=
  (n.divisors.filter fun m => Odd m ∧ ∃ d ∈ n.divisors, d < m ∧ m < 2 * d).card

abbrev Target : Prop :=
    ∀ (n : ℕ),
      a n = num2DenseSublists n

end Problem
