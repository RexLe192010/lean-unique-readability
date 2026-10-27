# Chapter 2 ↔ Lean: what maps to what

Two things live here: the map from the `.tex` sources to the Lean names, and the
list of defects the formalization forced out of the notes.

All `.tex` paths are relative to `2_propositional_logic/`. All Lean paths are
relative to `lean/PropLogic/`. All Lean names are in namespace `PropLogic` (the
restatements in `PropLogic.Chapter2`).

Results are named by the number they carry in the compiled notes (`main.pdf`).
Section numbers are the notes' own and do not line up with the `.tex` filenames.

§2.1–§2.2 span three Lean files. `Syntax/Basic.lean` holds the string-level
development — the two definitions of `Form` and their equivalence;
`Syntax/Trees.lean` holds the syntax tree `Fml` and `range_str`, which says the
trees render onto exactly `Form`; and `Syntax/UniqueReadability.lean` holds the
parenthesis calculus and `str_injective`. See the README's *Layout* section for
why the split falls where it does.

---

## Part 1 — The map

### §2.1 Syntax (`1_pl_syntax.tex`)

| Notes | Lean | File |
|---|---|---|
| **Definition 1** — `Form` = smallest closed set | `IsClosed`, `FormInter` | `Syntax/Basic.lean` |
| **Lemma 1** — `Form` exists, is unique | `isClosed_formInter`, `formInter_subset`, `form_unique` → `Chapter2.form_well_defined` | `Syntax/Basic.lean` |
| **Definition 2** — `Form' = ⋃ᵢ Formᵢ` | `stratum`, `Form` | `Syntax/Basic.lean` |
| **Claim 1** — `Form' = Form` | `formInter_eq_form` | `Syntax/Basic.lean` |

### §2.2 Unique Readability (`1_pl_syntax.tex`)

| Notes | Lean | File |
|---|---|---|
| **Definition 3** — primary connective, immediate subformulas | the constructors of `Fml`, via `range_str` | `Syntax/Trees.lean` |
| **Lemma 2** — balanced parentheses | `bal_str`, `nL_str_eq_nR_str` | `Syntax/UniqueReadability.lean` |
| **Lemma 3** — nonempty strict prefixes unbalanced | `one_le_bal_of_strict_prefix`, `nR_lt_nL_of_strict_prefix` | `Syntax/UniqueReadability.lean` |
| **Corollary 1** — a strict prefix is not a formula | `not_mem_form_of_strict_prefix`, `eq_of_str_prefix` | `Syntax/UniqueReadability.lean` |
| **Theorem 1** — Unique Readability | `str_injective`; notes' phrasing as `negStr_inj`, `binStr_inj`, `negStr_ne_binStr` | `Syntax/UniqueReadability.lean` |
| *(no counterpart)* — every prefix of a formula, strict or not, has balance ≥ 0 | `bal_nonneg_of_prefix`, with `prefix_bal_ge_singleton` / `prefix_bal_ge_append` | `Syntax/UniqueReadability.lean` |

The last row is the one place §2.2's formalization proves something the notes do
not state. The notes' only prefix lemma is **Lemma 3**, which is about *strict*
prefixes; the unrestricted form is what makes the induction go through, and
Lemma 3 follows from it. The module's section docstring *Every prefix of a
formula is non-negative* gives the argument.

<!-- ===========================================================================
SECTIONS BELOW ARE OUT OF SCOPE FOR THE CURRENT RELEASES AND ARE COMMENTED OUT.

Lean Project 0 covers §2.1 (`Syntax/Basic.lean`); Lean Project 1 covers §2.2
(`Syntax/Trees.lean`, `Syntax/UniqueReadability.lean`). Everything from §2.3
onward — Semantics, Satisfiability and Validity, SAT Solving, 3-Colorability,
Validity, Resolution — belongs to later projects. The rows are kept verbatim,
not deleted: uncomment a section when its project is released, and re-check the
Lean names against the files at that point.
============================================================================ -->
<!--
### §2.3 Semantics (`2_pl_semantics.tex`)

| Notes | Lean | File |
|---|---|---|
| **Definition 4** — assignment | `Assign P := P → Bool` | `Semantics/Basic.lean` |
| **Definition 5** — satisfies, `v ⊨ φ` | `Sat`, notation `v ⊨ φ` | `Semantics/Basic.lean` |
| **Definition 6** — value, `v[φ]` | `value` | `Semantics/Basic.lean` |
| **Lemma 4** — `v ⊨ φ` iff `v[φ] = T` | `sat_iff_value` | `Semantics/Basic.lean` |

### §2.4 Satisfiability and Validity (`2_pl_semantics.tex`)

| Notes | Lean | File |
|---|---|---|
| **Definition 7** — models | `models` | `Semantics/Models.lean` |
| **Definition 8** — semantic equivalence | `Equiv`, notation `≡ᶠ` | `Semantics/Models.lean` |
| **Definition 9** — satisfiable / unsatisfiable / valid | `Satisfiable`, `Unsatisfiable`, `Valid` | `Semantics/Models.lean` |
| **Lemma 5** — `φ` valid iff `(¬φ)` unsat | `valid_iff_neg_unsatisfiable` | `Semantics/Models.lean` |
| **Lemma 6** — `φ₁ ≡ φ₂` iff XOR unsat | `equiv_iff_xor_unsatisfiable` | `Semantics/Models.lean` |

### §2.5 SAT Solving (`3_pl_sat.tex`)

| Notes | Lean | File |
|---|---|---|
| **Definition 10** — the SAT problem | `Satisfiable` | `Semantics/Models.lean` |
| **Definitions 11–13** — literal, clause, CNF | `Lit`, `Clause`, `CNF` | `Resolution/Clause.lean` |
| **Algorithm 1** — Naive SAT | `naiveSat`, `naiveSat_correct` | `Semantics/Models.lean` |
| **Theorem 2** — Cook–Levin | *not formalized* (needs a machine model) | — |
| Eager-simplification tables | `negS`, `orS`, `andS`, `impS` + `value_*S` | `SAT/Simplify.lean` |
| `φ[p → c]` | `substE` | `SAT/Simplify.lean` |
| **Lemma 7** — Substitution Lemma | `value_substE` (sharp form), `substitution_lemma` (notes' form) | `SAT/Simplify.lean` |
| **Corollary 2** — split on `p` | `satisfiable_iff_substE` | `SAT/DPLL.lean` |
| **Algorithm 2** — DPLL | `dpll`, `dpll_correct`, `dpll_correct_fml` | `SAT/DPLL.lean` |
| Unit propagation / polarity heuristics | *not formalized* (search order, not answer) | — |

### §2.6 Encoding 3-Colorability as SAT (`4_sat_encoding.tex`)

| Notes | Lean | File |
|---|---|---|
| **Definition 14** — 3-COLOR | `ThreeColorable` | `SAT/ThreeColoring.lean` |
| Propositions `P_{ij}` | `ColorVar V := V × Fin 3` | `SAT/ThreeColoring.lean` |
| Constraints 1–3, `Ψ₁`, `Ψ₂`, `Ψ₃`, `Ψ` | `psi1`, `psi2`, `psi3`, `psi` | `SAT/ThreeColoring.lean` |
| "every vertex has exactly one colour" | `exists_unique_color` | `SAT/ThreeColoring.lean` |
| Size `6|E| + 9|V|` | `card_psi_le` | `SAT/ThreeColoring.lean` |
| **Claim 2** — `G` 3-colorable iff `Ψ ∈ SAT` | `threeColorable_iff_satisfiable` | `SAT/ThreeColoring.lean` |

### §2.7 Validity (`5_validity.tex`)

| Notes | Lean | File |
|---|---|---|
| **Definition 15** — validity | `Valid` | `Semantics/Models.lean` |
| **Algorithm 3** — Naïve VALID | `naiveValid`, `naiveValid_correct` | `Semantics/Models.lean` |
| `NOT-VALID` has a witness | `not_valid_iff_exists_countermodel` | `Semantics/Models.lean` |
| `VALID ∈ EXPTIME / PSPACE`, `NOT-VALID ∈ NP` | *not formalized* (needs a machine model) | — |

### §2.8 Resolution (`6_propositional_resolution.tex`, `7_resolution_soundness_completeness.tex`)

PROVISIONAL NUMBERS. `0_header.tex` does not `\input` either of these files, so
nothing in the compiled notes carries the numbers below — they are what these
results will be numbered once the sections are added. Re-derive every one of them
from the `\newlabel` lines in `main.aux` before trusting this table. The same
caution applies to any section uncommented later: `5_validity.tex` was added on
14 September 2026, and the §2.6 numbers in this file had drifted (3-COLOR is
Definition 14, not 11 — Definitions 11-13 are literal, clause and CNF, from §2.5).

| Notes | Lean | File |
|---|---|---|
| Literals, clauses, CNF (**Definitions 11–13**, stated back in §2.5) | `Lit`, `Clause`, `CNF` (arlib convention) | `Resolution/Clause.lean` |
| **Definition 13** — the resolution rule | `resolvent` | `Resolution/Rule.lean` |
| **Lemma 8** — resolution preserves satisfiability | `resolvent_sat`; notes' biconditional as `sat_pair_iff_sat_resolvent` | `Resolution/Rule.lean` |
| **Definition 14** — size of the search space | *not formalized* (a counting remark) | — |
| **Definition 15** — resolution reduction procedure, and **Definition 16** — refutation | `Derivable`, `HasRefutation` | `Resolution/Completeness.lean` |
| **Lemma 9** — some proposition occurs in both polarities | `exists_opposite_polarity` | `Resolution/Completeness.lean` |
| `R_p(Φ)` | `Rp`, `Rp_vars_subset`, `derivable_of_mem_Rp` | `Resolution/Completeness.lean` |
| **Claim 3** — `R_p(Φ)` unsatisfiable | `Rp_unsatisfiable` | `Resolution/Completeness.lean` |
| **Theorem 3**, soundness | `unsatisfiable_of_hasRefutation` | `Resolution/Completeness.lean` |
| **Theorem 3**, completeness | `hasRefutation_of_unsatisfiable` | `Resolution/Completeness.lean` |
| **Theorem 3**, both directions | `unsatisfiable_iff_hasRefutation` | `Resolution/Completeness.lean` |
| **Theorem 4** — resolution requires `EXPSPACE` | *not formalized* — see defect 9 | — |

-->

<!---

## Part 2 — Defects found

> **Status: all of the defects below have been corrected in the `.tex` sources.**
> This section is kept as the record of what the formalization found and why the
> Lean statements carry the hypotheses they do. Line numbers refer to the
> sources *as they stood before the corrections*.

Classified by severity. **The chapter's results all stand**: every theorem is
true, and every one of them is proved here. The defects were missing hypotheses,
non-total definitions, and broken proofs of true statements — the things a
careful referee should have caught.

Only the two defects in §2.1–§2.2 are shown; the rest are commented out with the
sections they belong to. Defect numbers are left unchanged, so the visible ones
are **1** and **10a**.

### Genuine errors — the statement as written is false

**1. Lemma 3 is false for the empty prefix.**
`1_pl_syntax.tex:145`. The lemma asserts `#'(' φ > #')' φ` for *every* strict
prefix `φ` of a formula `θ`. But `ε` is a strict prefix of every formula and
`#'(' ε = #')' ε = 0`. The notes are aware of `ε` — at `1_pl_syntax.tex:142`
they explicitly list it among the strict prefixes of `abcd` — and the proof
quietly ducks it, saying the base case is "vacuously true since there are no
*non-trivial* strict prefixes."
*Fix:* add `t ≠ []`. Lean: `one_le_bal_of_strict_prefix` carries `hne : t ≠ []`.
*Impact: none downstream.* The only consumer is Corollary 1, which
is fine as stated, because `ε` is not a formula either — `nil_not_mem_form`
discharges the side condition. Recommend stating the lemma for nonempty strict
prefixes and remarking that `ε ∉ Form` handles the rest.

<!-- Defects 2-9 concern §2.3-§2.8 and are out of scope for Projects 0 and 1.
     Kept verbatim; uncomment alongside the section they belong to. The numbering
     of the surviving defects (1, 10a) is deliberately left unchanged so that
     references to a defect by number stay stable. -->
<!--
**2. Lemma 9 is false as stated.**
`7_resolution_soundness_completeness.tex:5`. "If `Φ_CNF` is unsatisfiable, then
there exists at least one proposition `p` appearing in opposite polarities in
two separate clauses." Counterexample: `Φ = {□}`, the CNF whose single clause is
empty. It is unsatisfiable and mentions no proposition at all.
*Fix:* add `□ ∉ Φ`. Lean: `exists_opposite_polarity` carries `hne : (∅ : Clause V) ∉ Φ`.
With that hypothesis the notes' own contrapositive argument goes through.

**3. `R_p(Φ)` does not eliminate `p`, so the completeness induction does not terminate.**
`7_resolution_soundness_completeness.tex:16` (and again at line 80). `R_p(Φ)` is
defined as the `p`-free clauses together with `{α ∪ β : α ∪ {p} ∈ Φ, β ∪ {¬p} ∈ Φ}`.
Read literally, a clause that is a `p`-tautology is allowed as *both* parents:
for `C = {p, ¬p}`, resolving `C` against itself gives `(C ∖ {p}) ∪ (C ∖ {¬p}) = C`.
So take `Φ = {{p, ¬p}, □}`, which is unsatisfiable. Then `R_p(Φ) = Φ`, `p`
survives, and line 82's "by construction, `R_p(Φ)` has at least one less
proposition than `Φ`" is false — which is exactly the fact the completeness
induction rests on.
*Fix:* restrict both families to non-tautological parents (`¬p ∉ α ∪ {p}` and
`p ∉ β ∪ {¬p}`). This is evidently the intent — §2.6 already writes
`c₁ = α ∪ {p}`, `c₂ = β ∪ {¬p}` with "`p, ¬p ∉ α, β`" — but §2.7's definition
drops it. Lean: `Rp` filters on `(p,true) ∈ C ∧ (p,false) ∉ C` and
`(p,false) ∈ D ∧ (p,true) ∉ D`; `Rp_vars_subset` then holds.

**4. The eager-simplification table for `→` is not total.**
`3_pl_sat.tex:88`. Its four rows are `φ₁ = F`, `φ₁ = T`, `φ₁ ∈ Form ∧ φ₂ = F`,
and `φ₁, φ₂ ∈ Form`. Nothing covers `φ₁ ∈ Form` with `φ₂ = T`, so `(q → p)[p → T]`
is simply undefined — the last row does not apply, since `T ∉ Form`. The missing
value is `T`. The root cause is visible by comparison: the `∨` and `∧` rows are
total because their constant rows range over *both* arguments ("`T` if `φ₁ = T`
**or** `φ₂ = T`"), whereas `→`'s row "`T` if `φ₁ = F`" ranges over the first only.
*Fix:* add the row `T if φ₂ = T`. Lean: `impS` covers it, and Lean's
exhaustiveness checker enforces totality.

**5. The eager-simplification table for `↔` is not total, and `↔` is not
a connective of this logic.** `3_pl_sat.tex:98`. No row covers `φ₁ ∈ Form` with
`φ₂ ∈ {T, F}` (e.g. `↔(p, T)`, which should be `p`). Independently, `↔` is not
in the alphabet declared in `1_pl_syntax.tex` — the connectives there are `¬`,
`∧`, `∨`, `→` — so the whole table is stray. *Fix:* drop it, or define `↔` as
the abbreviation the table's own last row gives.

**6. `5_validity.tex:20–21`: Algorithm 3 iterates over the wrong
set, and its comment is backwards.** Line 20 reads `\FOR{$\sigma \in \prop$}` —
it should range over assignments, `σ ⊆ Prop` (as Algorithm 1 correctly
does). Line 21's comment says "`Eval(φ, σ)` determines whether `φ ⊨ σ`"; the
relation is `σ ⊨ φ`.

**7. `7_resolution_soundness_completeness.tex:106,112`: the pigeonhole encoding
is wrong on both constraints.** With `P_{ij}` = "pigeon `i` is in hole `j`":
- Constraint 1 is written `⋀_{i∈[1,n]} ⋁_{j∈[1,n+1]} P_{ji}`, which says *every
  hole contains at least one pigeon* — not the intended "every pigeon is in at
  least one hole", which is `⋀_{i∈[1,n+1]} ⋁_{j∈[1,n]} P_{ij}`. The indices are
  transposed.
- Constraint 2 is written `⋀_{j∈[1,n]} ⋀_{(i,k)∈[1,n+1]} (¬P_{ij} ∨ ¬P_{kj})`
  with no `i ≠ k`. Taking `i = k` yields `¬P_{ij} ∨ ¬P_{ij} ≡ ¬P_{ij}`, which
  forces every variable false and makes the formula unsatisfiable for a reason
  that has nothing to do with pigeonholes.

### Broken proofs of true statements

**8. The proof of Claim 3 is not a proof.**
`7_resolution_soundness_completeness.tex:21–50`. It opens by assuming
`v ⊨ R_p(Φ)` and closes at line 50 by deriving `v ⊭ R_p(Φ)` and calling it a
contradiction — but the intervening steps do not establish that. Line 23
asserts "either the `α`'s are satisfiable, or the `β`'s are satisfiable" with a
justification that presupposes the conclusion, and line 32 (`So, Φ: p, ¬p ∈ γ`)
is not parseable as a claim.
*The statement is true.* The clean argument, which is what
`Rp_unsatisfiable` formalizes: given `v ⊨ R_p(Φ)`, let `v_F`, `v_T` extend `v`
by `p ↦ F`, `p ↦ T`. Both fail `Φ`, so pick `C ∈ Φ` failing under `v_F` and
`D ∈ Φ` failing under `v_T`. Then `¬p ∉ C` (else `v_F ⊨ C`), and `C` cannot be
`p`-free (else `C ∈ R_p(Φ)`, so `v ⊨ C`, so `v_F ⊨ C`); hence `p ∈ C`.
Symmetrically `¬p ∈ D`. So the resolvent is in `R_p(Φ)` and `v` satisfies it —
but its satisfied literal is `p`-free and so survives into `v_F` or `v_T`,
contradicting the choice of `C` or `D`. Note this last step is precisely where
tautology-freeness (defect 3) is needed.

**9. The proof of Theorem 4 establishes nothing.**
`7_resolution_soundness_completeness.tex:91`. The claim is "Resolution requires
`EXPSPACE` in the worst case". The proof sets up the pigeonhole formula, then
does the `n = 1` case and refutes it in three steps, concluding "these
constraints provide conclusive evidence that the statement is indeed
unsatisfiable" — i.e. it shows one small instance is unsatisfiable, which is not
a lower bound of any kind. No asymptotics appear anywhere. The intended result
is presumably Haken's theorem: every resolution refutation of `PHP_n` has size
`2^{Ω(n)}`. That is a substantial theorem and is not proved here; the notes
should either cite it or drop the claim. (Note also the mismatch of measure —
the section header says `EXPSPACE`, while Haken's bound is on refutation
*size*.)


### Minor / editorial

**10a. A cross-reference to Definition 1 resolves to "Definition 30".**
`1_pl_syntax.tex`, in the two places that refer back to the non-constructive
definition of `Form`. The environment that introduces it is Definition 1, but
both in-text references render as "Definition 30", so a reader is sent to a
definition that does not exist. The Lean files name it
**Definition 1**.

<!-- Defects 10-15 concern §2.3-§2.8; out of scope for Projects 0 and 1. -->
<!--
**10. Duplicate LaTeX label.** `theorem:resolution-theorem` is used twice, at
`7_resolution_soundness_completeness.tex:55` and `:91`, so
`\ref{theorem:resolution-theorem}` resolves to the second one and every
cross-reference to the soundness/completeness theorem silently points at the
`EXPSPACE` theorem instead.

**11. No simplification table for `¬`.** `3_pl_sat.tex:60` gives
`φ[p→c] = (¬ φ'[p→c])` for `φ = (¬φ')`. Taken literally this produces `(¬T)`,
which is not in `Form` and, worse, is a compound node rather than a syntactic
constant — so the enclosing `∨`/`∧`/`→` tables, which test for syntactic `T`/`F`,
never fire, and eager simplification silently stops propagating. The one-line
table `¬T = F`, `¬F = T` is needed. Lean: `negS`.

**12. `6_propositional_resolution.tex:8` (Definition 13): `p, ¬p ⊄ α, β`**
uses `⊄` where `∉` is meant (`p` is a literal, not a set).

**13. `2_pl_semantics.tex:99`**: the third case of the Lemma 4
proof is labelled "Or:" but proves the `∧` case (line 97 is the genuine `∨` case).

**14. `3_pl_sat.tex:11–19`, Algorithm 1**: the algorithm computes `B` but
never returns it, and so has no output despite the caption promising
"SAT or UNSAT".

**15. `7_resolution_soundness_completeness.tex:74`**: Theorem 3's completeness base case
reads "`|Prop| = 0`, i.e., an empty clause of a formula with an empty clause is
trivially unsatisfiable". Beyond being garbled, the case needs the observation
that `Φ ≠ ∅` — the empty *set of clauses* is satisfiable — so that from "every
clause is empty" one gets `□ ∈ Φ`. Lean: `empty_mem_of_vars_eq_empty`.
-->
