/-
Copyright (c) 2026 Suguman Bansal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suguman Bansal
-/
/-
# PropLogic — Chapter 2 of CS 8803, machine-checked

A Lean 4 + Mathlib formalization of Chapter 2 ("Propositional Logic") of the
CS 8803 *Logic in Computer Science* lecture notes: syntax and unique
readability, semantics, satisfiability and validity, eager simplification and
DPLL, the reduction of 3-colorability to SAT, and the soundness and completeness
of propositional resolution.

Importing `PropLogic` pulls in the whole development.  `PropLogic.Chapter2`
restates every result of the chapter in one file, in the chapter's own order and
under the chapter's own labels; start there.

## Layout

* `PropLogic.Syntax.Basic` — the alphabet, the strata `Formᵢ`, the
  non-constructive "smallest closed set" definition, their equivalence, and the
  bridge between formula *strings* and formula *trees*.
-- * `PropLogic.Syntax.UniqueReadability` — parenthesis counting, the prefix
--   lemmas, and the Unique Readability Theorem.
-- * `PropLogic.Semantics.Basic` — assignments, `v ⊨ φ`, `v[φ]`, and their
--   agreement.
-- * `PropLogic.Semantics.Models` — models, semantic equivalence, satisfiable /
--   unsatisfiable / valid, and the naive SAT and VALID algorithms.
-- * `PropLogic.SAT.Simplify` — formulas with constants, eager simplification, and
--   the Substitution Lemma.
-- * `PropLogic.SAT.DPLL` — the splitting corollary and DPLL's correctness.
-- * `PropLogic.SAT.ThreeColoring` — 3-COLOR ≤ SAT and its correctness.
-- * `PropLogic.Resolution.Clause` — literals, clauses, CNF and their semantics
--   (following arlib's clause conventions).
-- * `PropLogic.Resolution.Rule` — the resolution rule and that it preserves
--   satisfiability.
-- * `PropLogic.Resolution.Completeness` — resolution derivations, the `R_p`
--   construction, soundness and completeness.
-- * `PropLogic.Chapter2` — the capstone: every result of the chapter, restated.
-/
import PropLogic.Syntax.Basic
-- import PropLogic.Syntax.Trees
-- import PropLogic.Syntax.UniqueReadability
-- import PropLogic.Semantics.Basic
-- import PropLogic.Semantics.Models
-- import PropLogic.SAT.Simplify
-- import PropLogic.SAT.DPLL
-- import PropLogic.SAT.ThreeColoring
-- import PropLogic.Resolution.Clause
-- import PropLogic.Resolution.Rule
-- import PropLogic.Resolution.Completeness
-- import PropLogic.Chapter2
