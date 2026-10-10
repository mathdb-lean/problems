import Mathlib
/-
Copyright 2026 OpenAI. Licensed under the Apache License, Version 2.0.
Copyright 2026 The mathdb-lean Authors.

The definitions and the statements below are OpenAI's, from
github.com/openai/math at the revision named in the metadata block; see NOTICE.
What this library changed: each `sorry`-bodied theorem became the definition of
the proposition it stated, and `Problem.Target` conjoins those propositions.

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

/-!
Converted from github.com/openai/math. `source_locator` names the comparator
challenge this came from and `source_solution_module` the module there that
proves it; both are at `source_version`. The definitions are the challenge's
own; each sorried theorem became `<name>_statement`, and `Problem.Target`
below conjoins them. `track` is solved because comparator accepted OpenAI's
proof against this very statement. Whether the statement says what the paper's
title says is what the scope note, carried as a caveat, is about.

- problem_id: MinUncut
- collection: openai-math
- question_id: openai-math:102
- source: openai-math
- source_locator: lean/ComparatorChallenges/MinUncut.lean#OAI.MinUncut.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves Khot's Unique Games Conjecture. Independent direct reductions also establish NP-hardness, on unweighted graphs, of approximation beyond the Goemans–Williamson ratio for Max-Cut, below factor two for Vertex Cover, and within any fixed constant factor for Min-UnCut and directed feedback vertex set. These direct proofs use established PCP and Label Cover hardness results. ([Lean](lean/docs/102.md)) We prove the Unique Games Conjecture. For every fixed $`\varepsilon,\delta\in(0,1/2)`$, we give a deterministic polynomial-time reduction from 3SAT to Unique Games over a fixed finite alphabet, with completeness at least $`1-\varepsilon`$ and soundness at most δ. We prove that approximating Max-Cut on simple unweighted graphs within any fixed factor greater than the Goemans–Williamson constant is NP-hard. We prove that minimum Vertex Cover is NP-hard to approximate within every fixed factor below two, even on simple unweighted graphs. For every fixed C &gt; 1, approximating Min-UnCut within factor C is NP-hard, even on simple undirected unweighted graphs. Approximating minimum directed feedback vertex set within any fixed constant factor is NP-hard, even on unweighted digraphs.
- notes: OpenAI math result family 102, The Unique Games Conjecture and optimal approximation thresholds -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/102.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.MinUncut.main
- source_theorem_count: 1
- source_solution_module: OAI.Computability.MinUncut.Main
- source_papers: preprints/The-Unique-Games-Theorem-September-23-2026/paper.pdf preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf preprints/The-Factor-Two-Hardness-Threshold-for-Vertex-Cover-September-23-2026/paper.pdf preprints/Constant-factor-hardness-of-Min-UnCut-September-23-2026/paper.pdf preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf
- source_scope_note: lean/docs/102.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

   
                                                                         
                                                                

                                                                          
                                                                         
                                                                        
                                                                      
  
namespace MinUncutGames.BinaryFormula

structure Literal where
  name : Nat
  positive : Bool
  deriving DecidableEq

def Literal.eval (literal : Literal) (assignment : Nat → Bool) : Bool :=
  if literal.positive then assignment literal.name else !(assignment literal.name)

abbrev Clause := Vector Literal 3

def Clause.eval (clause : Clause) (assignment : Nat → Bool) : Bool :=
  (clause[0].eval assignment || clause[1].eval assignment) || clause[2].eval assignment

structure Formula where
  clauses : List Clause

def Formula.Satisfiable (F : Formula) : Prop :=
  ∃ assignment : Nat → Bool, ∀ clause ∈ F.clauses, clause.eval assignment = true

end MinUncutGames.BinaryFormula

namespace MinUncutGames.BinaryEncoding
open BinaryFormula

def frame : List Bool → List Bool
  | [] => [false]
  | b :: bits => true :: b :: frame bits

def nameBits (name : Nat) : List Bool := frame name.bits

def literalBits (literal : Literal) : List Bool :=
  literal.positive :: nameBits literal.name

def clauseBits (clause : Clause) : List Bool :=
  literalBits clause[0] ++ literalBits clause[1] ++ literalBits clause[2]

def clausesBits : List Clause → List Bool
  | [] => [false]
  | clause :: clauses => true :: (clauseBits clause ++ clausesBits clauses)

def formulaBits (formula : Formula) : List Bool := clausesBits formula.clauses

end MinUncutGames.BinaryEncoding

namespace MinUncut
open MinUncutGames.BinaryFormula MinUncutGames.BinaryEncoding

                                                                        
                                                                           
structure Output where
  vertices : ℕ
  adjacent : Fin vertices → Fin vertices → Bool
  symmetric : ∀ u v, adjacent u v = adjacent v u
  loopless : ∀ u, adjacent u u = false
  threshold : ℕ
  threshold_pos : 1 ≤ threshold

                                                                              
                                                           
def Output.uncut (G : Output) (cut : Fin G.vertices → Bool) : ℕ :=
  (Finset.univ.filter fun uv : Fin G.vertices × Fin G.vertices =>
    uv.1 < uv.2 ∧ G.adjacent uv.1 uv.2 = true ∧ cut uv.1 = cut uv.2).card

                                                                             
                                     
noncomputable def Output.opt (G : Output) : ℕ :=
  (Finset.univ.image G.uncut).min' (by
    exact Finset.image_nonempty.mpr Finset.univ_nonempty)

                                                                        
                                                                           
def Output.bits (G : Output) : List Bool :=
  nameBits G.vertices ++
    ((List.finRange G.vertices).flatMap fun u =>
      (List.finRange G.vertices).map fun v => G.adjacent u v) ++
    nameBits G.threshold

                                                                               
                                                             
def inputBits (input : ℕ × Formula) : List Bool :=
  nameBits input.1 ++ formulaBits input.2

                                                                            
                                                                         
                                                                       
                                                                 
structure Reduction where
  reduce : ℕ → Formula → Output
  machine : Turing.TM2Computable inputBits Output.bits (fun p => reduce p.1 p.2)
  finiteAlphabet : ∀ k : machine.tm.K, Finite (machine.tm.Γ k)
  time : ℕ → Polynomial ℕ
  runtime : ∀ K φ,
    Turing.TM2OutputsInTime machine.tm
      ((inputBits (K, φ)).map machine.inputAlphabet.symm)
      (some (((reduce K φ).bits).map machine.outputAlphabet.symm))
      ((time K).eval (formulaBits φ).length)
  size : ℕ → Polynomial ℕ
  output_size : ∀ K φ,
    (reduce K φ).vertices + (reduce K φ).bits.length ≤
      (size K).eval (formulaBits φ).length
  yes : ∀ K, 2 ≤ K → ∀ φ, φ.Satisfiable →
    (reduce K φ).opt ≤ (reduce K φ).threshold
  no : ∀ K, 2 ≤ K → ∀ φ, ¬ φ.Satisfiable →
    K * (reduce K φ).threshold < (reduce K φ).opt

end MinUncut

namespace MinUncut

def main_statement : Prop :=
  Nonempty Reduction

end MinUncut

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.MinUncut.main_statement

end Problem

/- Formalization scope, from lean/docs/102.md: The Unique Games conjecture asks for hardness of distinguishing nearly satisfiable unique games from games of very small value. The formalized result gives, for every fixed $0<\varepsilon,\delta<1/2$, a deterministic polynomial-time reduction from binary 3SAT to nonempty unweighted simple bipartite unique games. Satisfiable inputs have value at least $1-\varepsilon$ and unsatisfiable inputs have value at most $\delta$. The alphabet is a fixed $\mathbb F_2^s$ depending only on the errors, and every constraint is a translation. The formalized result establishes hardness of approximating Max-Cut beyond the Goemans–Williamson constant $\alpha_{\mathrm{GW}}$. For every fixed $\alpha_{\mathrm{GW}}<\alpha\le1$, it gives a deterministic polynomial-time reduction from binary 3SAT to a strictly separated Max-Cut gap on finite simple unweighted graphs. The reduction includes the explicit positive integer scaling used in the gap statement. The formalized result gives the factor-two hardness threshold for Vertex Cover. For each integer $m\ge4$, a polynomial-time reduction from binary 3SAT produces simple unweighted graphs with cover density below $1/2+1/m$ on satisfiable inputs and above $1-1/m$ on unsatisfiable inputs. Consequently, any polynomial-time approximation with a fixed factor $1\le\alpha<2$ would give a polynomial-time decision algorithm for 3SAT. No assumption that $P\ne NP$ is built into the statement. Min-UnCut minimizes the number of edges left uncut by a bipartition. The formalization constructs a deterministic reduction from encoded $3$-SAT formulas to finite simple unweighted Min-UnCut instances with arbitrarily large fixed multiplicative gaps. For every integer $K\ge2$, satisfiable formulas give optimum at most the output threshold, while unsatisfiable formulas give optimum strictly greater than $K$ times that threshold. Runtime and output length are polynomial for each fixed $K$, establishing hardness for every fixed approximation factor greater than one. A directed feedback vertex set meets every directed cycle. The formalization proves hardness of approximating the minimum such set within any fixed constant factor. For every real factor $A\ge1$ and every language in NP, it constructs a polynomial-time gap reduction to unweighted directed graphs with the stated completeness and soundness separation. Thus a fixed-factor polynomial-time approximation would imply a polynomial-time algorithm for every NP language. -/
