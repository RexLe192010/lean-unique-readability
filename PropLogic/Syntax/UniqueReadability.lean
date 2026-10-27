/-
Copyright (c) 2026 Suguman Bansal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suguman Bansal
-/
import PropLogic.Syntax.Trees

/-!
# Unique readability  —  LEAN PROJECT 1

Six proofs in this file have been replaced by `sorry`, each marked

    EXERCISE n

with a hint.  Restore them.  Do not change any definition or theorem
statement.  Three of them are single *cases* of two larger proofs: the
remaining cases are given, and they are your model — read them first.

Order of the exercises is roughly increasing difficulty; work top to bottom
through the list in the handout rather than through the file.

When you are done, `lake build` reports no `sorry`, and

    #print axioms PropLogic.str_injective

mentions only `propext`, `Classical.choice`, `Quot.sound`.

**Instructor note — not for distribution.**  Each `sorry` is followed by a
`/- SOLUTION n ... -/` block holding, verbatim, the proof it replaced.  This
file is the single source for both versions of the module: delete every
`SOLUTION` block to get the file students receive, or splice each one back over
its `sorry` to get the complete formalization.  Do not release the file with
the blocks still in it.

This file formalizes §2.2 ("Unique Readability") of the notes: the
parenthesis-counting lemmas **Lemma 2** and **Lemma 3**, their
**Corollary 1**, and the Unique Readability Theorem itself,
**Theorem 1**.  Numbering refers to the course notes (`main.pdf`).

## What "unique readability" means here

The chapter keeps two views of a formula, in two files: the string
(`Form P ⊆ Str P`), built in `Syntax/Basic.lean`, and the tree (`Fml P`), added
in `Syntax/Trees.lean` together with the rendering `Fml.str` and the theorem
`range_str : Set.range Fml.str = Form P` that connects them.  The notes' theorem — that a
non-atomic formula has a *unique* primary connective and *unique* immediate
subformulas (**Definition 3**) — is exactly the
statement that `Fml.str` is **injective**: a string is the rendering of at most
one tree, so reading off the primary connective and the immediate subformulas is
unambiguous.  That is `str_injective`, and `formEquiv` packages it together with
`range_str` as a bijection `Fml P ≃ Form P`.

The notes' own three-way phrasing of the case analysis is recorded separately as
`negStr_inj`, `binStr_inj` and `negStr_ne_binStr`.

## The counting argument

We count parentheses with `nL`/`nR` (the notes' `#'('` and `#')'`) and package
the two into the integer `bal = nL - nR`, which turns "same number of
parentheses" into "`bal = 0`" and, crucially, is *additive* over `++`.  The
argument is then:

* `bal_str` (**Lemma 2**): every formula is balanced.
* `bal_nonneg_of_prefix`: every prefix of a formula has `bal ≥ 0`.  This has no
  counterpart in the notes, whose only prefix lemma — **Lemma 3** — is about
  *strict* prefixes and says nothing about a prefix that is the whole formula.
  Dropping "strict" is precisely what makes the induction go through; the
  section docstring "Every prefix of a formula is non-negative" below says why.
* `one_le_bal_of_strict_prefix` (**Lemma 3**): every *nonempty*
  strict prefix has `bal ≥ 1`, i.e. `nR < nL`.
* `not_mem_form_of_strict_prefix` (**Corollary 1**) and
  `eq_of_str_prefix`: no strict prefix of a formula is a formula, so if one
  formula string is a prefix of another they are equal.  This is the only fact
  about strings that the main theorem needs.

## Why the prefix lemma excludes `ε`

**Lemma 3** requires its prefix to be nonempty, and the hypothesis
cannot be dropped: the notes count `ε` among the strict prefixes of a string (the
`y = abcd` example lists it first), and `#'(' ε = #')' ε = 0`, so the strict
inequality fails there.  `one_le_bal_of_strict_prefix` carries `t ≠ []`
accordingly.

The restriction costs nothing downstream.  Its only consumer is
**Corollary 1**, where the excluded case is harmless because `ε ∉ Form`
anyway (`nil_not_mem_form` in `Syntax/Trees.lean`).  That is how
`not_mem_form_of_strict_prefix` is proved below — the `t ≠ []` side condition is
discharged from `Fml.str_ne_nil` — so the corollary holds for *all* strict
prefixes, exactly as the notes state it.
-/

namespace PropLogic

universe u

variable {P : Type u}

/-! ## Counting parentheses

The notes write `#'a'(s)` for the number of occurrences of the character `a` in
the string `s`.  We use `List.countP` with `Bool`-valued predicates rather than
`List.count`, so that nothing here needs `DecidableEq P`. -/

/-- `true` exactly on the left parenthesis. -/
def isLpar : Sym P → Bool
  | Sym.lpar => true
  | _ => false

/-- `true` exactly on the right parenthesis. -/
def isRpar : Sym P → Bool
  | Sym.rpar => true
  | _ => false

/-- The notes' `#'('(s)`: the number of left parentheses in `s`. -/
def nL (s : Str P) : ℕ := s.countP isLpar

/-- The notes' `#')'(s)`: the number of right parentheses in `s`. -/
def nR (s : Str P) : ℕ := s.countP isRpar

/-- The **parenthesis balance** `#'(' - #')'` of a string, as an integer.

Working with the difference rather than the pair is what makes the whole section
routine: `bal` is additive over concatenation (`bal_append`), so "`θ` is
balanced" and "every prefix of `θ` is non-negative" compose across the
concatenations in `negStr`/`binStr` with no case analysis. -/
def bal (s : Str P) : ℤ := (nL s : ℤ) - (nR s : ℤ)

@[simp] theorem bal_nil : bal ([] : Str P) = 0 := by simp [bal, nL, nR]

/-- Balance is additive over concatenation. This is the engine of the section. -/
@[simp] theorem bal_append (a b : Str P) : bal (a ++ b) = bal a + bal b := by
  simp [bal, nL, nR, List.countP_append]
  ring

@[simp] theorem bal_lpar : bal ([Sym.lpar] : Str P) = 1 := by
  simp [bal, nL, nR, List.countP_cons, isLpar, isRpar]

@[simp] theorem bal_rpar : bal ([Sym.rpar] : Str P) = -1 := by
  simp [bal, nL, nR, List.countP_cons, isLpar, isRpar]

@[simp] theorem bal_var (p : P) : bal ([Sym.var p] : Str P) = 0 := by
  simp [bal, nL, nR, List.countP_cons, isLpar, isRpar]

@[simp] theorem bal_negSym : bal ([Sym.neg] : Str P) = 0 := by
  simp [bal, nL, nR, List.countP_cons, isLpar, isRpar]

@[simp] theorem bal_connSym (c : Conn) : bal ([Sym.conn c] : Str P) = 0 := by
  simp [bal, nL, nR, List.countP_cons, isLpar, isRpar]

/-! ## Prefix combinatorics

The notes' `x ≼ y` ("`x` is a prefix of `y`") is Mathlib's `x <+: y`, and `x ≺ y`
("strict prefix") is `x <+: y` together with `x ≠ y`.

The one combinatorial fact the section needs is that a prefix of a concatenation
either stops inside the left factor or swallows it whole — this is what lets us
peel `negStr`/`binStr` one piece at a time from the front, and is precisely the
case enumeration the notes perform by hand in the proof of
**Lemma 3**. -/

/-- A prefix of `l₁ ++ l₂` is either a prefix of `l₁`, or `l₁` followed by a
prefix of `l₂`.

This is the formal counterpart of the notes' enumeration "the strict prefixes of
`(λ₁ ∘ λ₂)` are `(`, `(λ₁'`, `(λ₁∘`, `(λ₁∘λ₂'`, `(λ₁∘λ₂`". -/
theorem prefix_append_cases {α : Type*} {l l₁ l₂ : List α} (h : l <+: l₁ ++ l₂) :
    l <+: l₁ ∨ ∃ t, t <+: l₂ ∧ l = l₁ ++ t := by
  induction l₁ generalizing l with
  | nil => exact Or.inr ⟨l, by simpa using h, by simp⟩
  | cons a l₁ ih =>
      obtain ⟨u, hu⟩ := h
      cases l with
      | nil => exact Or.inl List.nil_prefix
      | cons b l' =>
          rw [List.cons_append, List.cons_append] at hu
          injection hu with hhd htl
          subst hhd
          rcases ih ⟨u, htl⟩ with hp | ⟨t, ht, hv⟩
          · obtain ⟨v, hv⟩ := hp
            exact Or.inl ⟨v, by rw [List.cons_append, hv]⟩
          · exact Or.inr ⟨t, ht, by rw [List.cons_append, hv]⟩

/-- A one-symbol string has exactly two prefixes: `ε` and itself. This is the
notes' base case "there are no non-trivial strict prefixes of a proposition". -/
theorem prefix_singleton_cases {α : Type*} {l : List α} {x : α} (h : l <+: [x]) :
    l = [] ∨ l = [x] := by
  obtain ⟨u, hu⟩ := h
  cases l with
  | nil => exact Or.inl rfl
  | cons a l' =>
      rw [List.cons_append] at hu
      injection hu with hhd htl
      subst hhd
      have hl' : l' = [] := by
        cases l' with
        | nil => rfl
        | cons c t => simp at htl
      exact Or.inr (by rw [hl'])

/-- If two concatenations agree, one left factor is a prefix of the other. This
is the dichotomy the notes appeal to in the last sub-case of
**Theorem 1** ("either `φ₁ ≺ φ₁'` or `φ₁' ≺ φ₁`"). -/
/- EXERCISE 6  This one has no close sibling in the file; build it from
   scratch.

   * `l <+: m` unfolds to `∃ u, l ++ u = m`, so an anonymous constructor
     `⟨_, _⟩` proves a prefix claim: from `h : a ++ b = c ++ d` you can
     produce a proof of `a <+: c ++ d` in one term.
   * Feed that to `prefix_append_cases`. Its two branches are exactly the
     two disjuncts you must produce.
   * In the second branch the pattern `⟨t, _, rfl⟩` rewrites `c ++ t` for
     `a`; then `c <+: a` holds with witness `t`. -/
theorem prefix_or_prefix_of_append_eq {α : Type*} {a b c d : List α} (h : a ++ b = c ++ d) :
    a <+: c ∨ c <+: a := by
  obtain hp | ⟨t, ht, hv⟩ :=
    prefix_append_cases (l := a) (l₁ := c) (l₂ := d) ⟨b, h⟩
  · exact Or.inl hp
  · exact Or.inr ⟨t, hv.symm⟩


/-! ## **Lemma 2**: formulas are balanced -/

/-- **Lemma 2**, in balance form: every well-formed formula
has parenthesis balance `0`.

The notes' induction is over the strata `Formᵢ`; here it is the structural
induction over `Fml P`, which is the same induction (`Fml.depth` is the stratum
index).  Each of `negStr`/`binStr` contributes exactly one `(` and one `)`. -/
/- EXERCISE 3  One of the three cases of **Lemma 2**; the `atom` and `neg`
   cases are given.  Read the `neg` case first — it is the model.  Yours is the
   same shape, but the string is `binStr`, the symbol between the subformulas
   is a connective, and there are now *two* induction hypotheses to rewrite
   with. -/
theorem bal_str (φ : Fml P) : bal φ.str = 0 := by
  induction φ with
  | atom p => simp
  | neg ψ ih =>
      simp only [Fml.str_neg, negStr, bal_append, bal_lpar, bal_negSym, bal_rpar, ih]
      ring
  | bin c φ₁ φ₂ ih₁ ih₂ =>
    simp only [Fml.str_bin, binStr, bal_append, bal_lpar, bal_connSym, bal_rpar, ih₁, ih₂]
    ring

/-- **Lemma 2** verbatim: `#'('(θ) = #')'(θ)` for every
`θ ∈ Form`. -/
theorem nL_str_eq_nR_str (φ : Fml P) : nL φ.str = nR φ.str := by
  have h := bal_str φ
  unfold bal at h
  omega

/-! ## Every prefix of a formula is non-negative

The notes state no lemma about arbitrary prefixes: their only prefix lemma,
**Lemma 3**, is about *strict* prefixes.  This statement drops that
restriction, because the unrestricted form is the induction hypothesis their
proof of **Lemma 3** actually needs: the cases "`(¬λ'` where `λ' ≺ λ`" and
"`(λ₁'` where `λ₁' ≺ λ₁`" appeal to the inductive hypothesis about *strict*
prefixes, while the cases "`(¬λ`" and "`(λ₁∘λ₂`" appeal to
**Lemma 2** about the *whole* subformula.  Unifying the two into
"every prefix, strict or not, is non-negative" removes the case split entirely,
and is also the statement that survives being pushed under the leading `(`. -/

/-- Compose a non-negativity bound across a concatenation whose left factor is
balanced. Used with `k = -1` (under a leading `(`) and `k = 0`. -/
private theorem prefix_bal_ge_append {k : ℤ} {a b : Str P}
    (ha : ∀ t, t <+: a → k ≤ bal t) (h0 : bal a = 0)
    (hb : ∀ t, t <+: b → k ≤ bal t) : ∀ t, t <+: a ++ b → k ≤ bal t := by
  intro t ht
  rcases prefix_append_cases ht with h | ⟨u, hu, rfl⟩
  · exact ha t h
  · rw [bal_append, h0, zero_add]
    exact hb u hu

/-- The base case of the composition above: a one-symbol string. -/
private theorem prefix_bal_ge_singleton {k : ℤ} {x : Sym P} (hk0 : k ≤ 0)
    (hkx : k ≤ bal [x]) : ∀ t, t <+: [x] → k ≤ bal t := by
  intro t ht
  rcases prefix_singleton_cases ht with rfl | rfl
  · simpa using hk0
  · exact hkx

/-- **Every prefix of a formula has non-negative parenthesis balance**, i.e. you
can never have closed more parentheses than you have opened while reading a
formula left to right.

Proof shape: a prefix of `( REST` is either `ε` (balance `0`) or `(` followed by
a prefix of `REST`, so it suffices that every prefix of `REST` has balance
`≥ -1`; and `REST` is a concatenation of one-symbol strings, whole subformula
strings (balance `0` by `bal_str`, prefixes `≥ 0` by the induction hypothesis)
and a final `)` (balance `-1`).

This is the induction hypothesis for `one_le_bal_of_strict_prefix`; it is proved
first, as a finished theorem, and used there as a black box. -/
theorem bal_nonneg_of_prefix (φ : Fml P) : ∀ {t : Str P}, t <+: φ.str → 0 ≤ bal t := by
  induction φ with
  | atom p =>
      intro t ht
      rcases prefix_singleton_cases ht with rfl | rfl <;> simp
  | neg ψ ih =>
      intro t ht
      rw [Fml.str_neg, negStr] at ht
      have h1 : ∀ v, v <+: ψ.str → (-1 : ℤ) ≤ bal v := fun v hv => le_trans (by norm_num) (ih hv)
      have h2 : ∀ v : Str P, v <+: [Sym.rpar] → (-1 : ℤ) ≤ bal v :=
        prefix_bal_ge_singleton (by norm_num) (by simp)
      have h3 := prefix_bal_ge_append h1 (bal_str ψ) h2
      have h4 : ∀ v : Str P, v <+: [Sym.neg] → (-1 : ℤ) ≤ bal v :=
        prefix_bal_ge_singleton (by norm_num) (by simp)
      have hrest := prefix_bal_ge_append h4 (by simp) h3
      rcases prefix_append_cases ht with h | ⟨u, hu, rfl⟩
      · rcases prefix_singleton_cases h with rfl | rfl <;> simp
      · have := hrest u hu
        rw [bal_append, bal_lpar]
        omega
  | bin c φ₁ φ₂ ih₁ ih₂ =>
      intro t ht
      rw [Fml.str_bin, binStr] at ht
      have h1 : ∀ v : Str P, v <+: [Sym.rpar] → (-1 : ℤ) ≤ bal v :=
        prefix_bal_ge_singleton (by norm_num) (by simp)
      have h2 : ∀ v, v <+: φ₂.str → (-1 : ℤ) ≤ bal v := fun v hv => le_trans (by norm_num) (ih₂ hv)
      have h3 := prefix_bal_ge_append h2 (bal_str φ₂) h1
      have h4 : ∀ v : Str P, v <+: [Sym.conn c] → (-1 : ℤ) ≤ bal v :=
        prefix_bal_ge_singleton (by norm_num) (by simp)
      have h5 := prefix_bal_ge_append h4 (by simp) h3
      have h6 : ∀ v, v <+: φ₁.str → (-1 : ℤ) ≤ bal v := fun v hv => le_trans (by norm_num) (ih₁ hv)
      have hrest := prefix_bal_ge_append h6 (bal_str φ₁) h5
      rcases prefix_append_cases ht with h | ⟨u, hu, rfl⟩
      · rcases prefix_singleton_cases h with rfl | rfl <;> simp
      · have := hrest u hu
        rw [bal_append, bal_lpar]
        omega

/-! ## **Lemma 3**: nonempty strict prefixes are unbalanced -/

/-- The strict-prefix analogue of `prefix_bal_ge_append`: only the *last* factor
of a concatenation gets to keep its "not the whole thing" side condition. -/
private theorem prefix_bal_nonneg_append_strict {a b : Str P}
    (ha : ∀ t, t <+: a → 0 ≤ bal t) (h0 : bal a = 0)
    (hb : ∀ t, t <+: b → t ≠ b → 0 ≤ bal t) :
    ∀ t, t <+: a ++ b → t ≠ a ++ b → 0 ≤ bal t := by
  intro t ht hne
  rcases prefix_append_cases ht with h | ⟨u, hu, rfl⟩
  · exact ha t h
  · have hub : u ≠ b := fun h => hne (by rw [h])
    rw [bal_append, h0, zero_add]
    exact hb u hu hub

/-- The innermost base case: the only strict prefix of the final `)` is `ε`.
This is where the trailing right parenthesis is kept *out* of the prefix, which
is exactly why a strict prefix stays non-negative. -/
private theorem prefix_bal_nonneg_rpar_strict :
    ∀ t : Str P, t <+: [Sym.rpar] → t ≠ [Sym.rpar] → 0 ≤ bal t := by
  intro t ht hne
  rcases prefix_singleton_cases ht with rfl | rfl
  · simp
  · exact absurd rfl hne

/-- **Lemma 3**: every *nonempty* strict prefix `t` of a
formula `θ` satisfies `#'(' t > #')' t`, here in balance form `1 ≤ bal t`.

The hypothesis `hne : t ≠ []` is necessary — `bal ε = 0`, and `ε` is a strict
prefix of every formula — and costs nothing downstream; see the module
docstring.

### Proof

Structural induction on `φ`, using the already-finished
`bal_nonneg_of_prefix` for the immediate subformulas.  For an atom there are no
nonempty strict prefixes.  Otherwise `t = ( t₀` and it suffices that
`0 ≤ bal t₀`; peeling `t₀` piece by piece, every branch gives `0 ≤ bal t₀` from
`bal_nonneg_of_prefix` or `bal_str`, except the branch that includes the closing
`)`, and that branch forces `t = φ.str`, contradicting `hlt`. -/
theorem one_le_bal_of_strict_prefix (φ : Fml P) {t : Str P}
    (hpre : t <+: φ.str) (hne : t ≠ []) (hlt : t ≠ φ.str) : 1 ≤ bal t := by
  induction φ generalizing t with
  | atom p =>
      rw [Fml.str_atom] at hpre hlt
      rcases prefix_singleton_cases hpre with rfl | rfl
      · exact absurd rfl hne
      · exact absurd rfl hlt
  | neg ψ _ =>
      rw [Fml.str_neg, negStr] at hpre hlt
      have h1 := prefix_bal_nonneg_append_strict (fun v hv => bal_nonneg_of_prefix ψ hv)
        (bal_str ψ) prefix_bal_nonneg_rpar_strict
      have hrest := prefix_bal_nonneg_append_strict
        (prefix_bal_ge_singleton (k := (0 : ℤ)) (x := (Sym.neg : Sym P)) le_rfl (by simp))
        (by simp) h1
      rcases prefix_append_cases hpre with h | ⟨u, hu, rfl⟩
      · rcases prefix_singleton_cases h with rfl | rfl
        · exact absurd rfl hne
        · simp
      · have hu' : u ≠ [Sym.neg] ++ (ψ.str ++ [Sym.rpar]) := fun h => hlt (by rw [h])
        have := hrest u hu hu'
        rw [bal_append, bal_lpar]
        omega
  | bin c φ₁ φ₂ _ _ =>
      rw [Fml.str_bin, binStr] at hpre hlt
      have h1 := prefix_bal_nonneg_append_strict (fun v hv => bal_nonneg_of_prefix φ₂ hv)
        (bal_str φ₂) prefix_bal_nonneg_rpar_strict
      have h2 := prefix_bal_nonneg_append_strict
        (prefix_bal_ge_singleton (k := (0 : ℤ)) (x := (Sym.conn c : Sym P)) le_rfl (by simp))
        (by simp) h1
      have hrest := prefix_bal_nonneg_append_strict (fun v hv => bal_nonneg_of_prefix φ₁ hv)
        (bal_str φ₁) h2
      rcases prefix_append_cases hpre with h | ⟨u, hu, rfl⟩
      · rcases prefix_singleton_cases h with rfl | rfl
        · exact absurd rfl hne
        · simp
      · have hu' : u ≠ φ₁.str ++ ([Sym.conn c] ++ (φ₂.str ++ [Sym.rpar])) :=
          fun h => hlt (by rw [h])
        have := hrest u hu hu'
        rw [bal_append, bal_lpar]
        omega

/-- **Lemma 3** in the notes' own notation: for a nonempty
strict prefix `t` of a formula, `#')'(t) < #'('(t)`.  See
`one_le_bal_of_strict_prefix` for why `t ≠ []` is required. -/
theorem nR_lt_nL_of_strict_prefix (φ : Fml P) {t : Str P}
    (hpre : t <+: φ.str) (hne : t ≠ []) (hlt : t ≠ φ.str) : nR t < nL t := by
  have h := one_le_bal_of_strict_prefix φ hpre hne hlt
  unfold bal at h
  omega

/-! ## **Corollary 1**: a strict prefix of a formula is not a formula -/

/-- **Corollary 1**: no strict prefix of a formula is itself a
formula.

Note that this holds for *every* strict prefix, including `t = ε`, even though
`one_le_bal_of_strict_prefix` has to exclude `ε`: if `t` were a formula it would
be some `χ.str`, and `Fml.str_ne_nil` rules out `t = ε` on the spot.  So the
nonemptiness side condition does not propagate. -/
/- EXERCISE 5  **Corollary 1** itself. Four given results have to meet in
   five lines; naming them is most of the work.

   * The goal `t ∉ Form P` is `t ∈ Form P → False`, so start with `intro`.
   * A membership in `Form P` becomes a tree via
     `mem_form_iff_exists_fml.mp`; `obtain ⟨χ, rfl⟩` names it and rewrites
     `t` as `χ.str` everywhere.
   * Now `one_le_bal_of_strict_prefix` applies — its `t ≠ []` side condition
     is exactly `χ.str_ne_nil`, which is why the corollary needs no
     nonemptiness hypothesis of its own.
   * But **Lemma 2** says that same string is balanced. `omega` finishes. -/
theorem not_mem_form_of_strict_prefix {φ : Fml P} {t : Str P}
    (hpre : t <+: φ.str) (hlt : t ≠ φ.str) : t ∉ Form P := by
  intro ht
  obtain ⟨χ, rfl⟩ := mem_form_iff_exists_fml.mp ht
  have hne := Fml.str_ne_nil χ
  have h := one_le_bal_of_strict_prefix φ hpre hne hlt
  have hbal := bal_str χ
  omega


/-- The form of **Corollary 1** used in the main theorem: if one formula
string is a prefix of another, the two are equal. There is no room for a formula
to be a proper initial segment of a formula. -/
theorem eq_of_str_prefix {φ ψ : Fml P} (h : φ.str <+: ψ.str) : φ.str = ψ.str := by
  by_contra hne
  exact not_mem_form_of_strict_prefix h hne φ.str_mem_form

/-! ## First symbols

The notes' recurring side remark: "a formula can only start with `(` or with
`p ∈ P`". These three lemmas are that remark, and they are what kill the mixed
`(¬φ)` versus `(φ₁ ∘ φ₂)` cases of **Theorem 1**. -/

/-- No formula begins with `¬`. -/
theorem str_ne_cons_neg (φ : Fml P) (u : Str P) : φ.str ≠ Sym.neg :: u := by
  cases φ <;> simp [negStr, binStr]

/-- No formula begins with a binary connective. -/
theorem str_ne_cons_conn (φ : Fml P) (c : Conn) (u : Str P) : φ.str ≠ Sym.conn c :: u := by
  cases φ <;> simp [negStr, binStr]

/-- No formula begins with `)`. -/
theorem str_ne_cons_rpar (φ : Fml P) (u : Str P) : φ.str ≠ Sym.rpar :: u := by
  cases φ <;> simp [negStr, binStr]

/-- If a nonempty `l` is an initial segment of `a :: m`, then `l` itself starts
with `a`. Used to transfer "this string starts with `¬`" onto a subformula. -/
private theorem head_eq_of_append {α : Type*} {a : α} {l r m : List α} (hne : l ≠ [])
    (h : l ++ r = a :: m) : ∃ l', l = a :: l' := by
  cases l with
  | nil => exact absurd rfl hne
  | cons b l' =>
      rw [List.cons_append] at h
      injection h with hhd _
      exact ⟨l', by rw [hhd]⟩

/-! ## **Theorem 1**: the Unique Readability Theorem -/

/-- **Theorem 1**: every non-atomic formula has a
unique primary connective and unique immediate subformulas.

Formally: the rendering `Fml.str` of syntax trees as strings is **injective**, so
a formula string comes from at most one tree.  Since a tree records exactly the
primary connective and the immediate subformulas at its root, and since
`range_str` says the trees hit exactly `Form P`, injectivity *is* the notes'
statement — see `negStr_inj`, `binStr_inj` and `negStr_ne_binStr` below for the
notes' own three-way phrasing, and `formEquiv` for the packaged bijection.

The proof follows the notes' case analysis:

* atom versus compound: an atom is `p`, a compound starts with `(`.
* `(¬φ)` versus `(φ₁ ∘ φ₂)`: cancelling the leading `(` would force `φ₁` to begin
  with `¬`, impossible by `str_ne_cons_neg`.
* `(φ₁ ∘ φ₂)` versus `(ψ₁ ∘' ψ₂)`: cancelling `(` gives
  `φ₁.str ++ REST = ψ₁.str ++ REST'`, so one of `φ₁.str`, `ψ₁.str` is a prefix of
  the other (`prefix_or_prefix_of_append_eq`); by **Corollary 1**
  (`eq_of_str_prefix`) they must then be *equal*.  Cancelling them leaves
  `∘ = ∘'` and `φ₂.str = ψ₂.str`, and the induction hypotheses finish. -/
theorem str_injective : Function.Injective (Fml.str : Fml P → Str P) := by
  intro φ
  induction φ with
  | atom p =>
      intro ψ h
      cases ψ with
      | atom q =>
          rw [Fml.str_atom, Fml.str_atom] at h
          injection h with hhd _
          injection hhd with hp
          rw [hp]
      | neg ψ => rw [Fml.str_atom, Fml.str_neg, negStr] at h; simp at h
      -- EXERCISE 1  Same shape as the `neg` line directly above: expose both
      -- strings with `rw`, and let `simp` see that a one-symbol string cannot
      -- equal one that begins with `(`.
      | bin d ψ₁ ψ₂ => rw [Fml.str_atom, Fml.str_bin, binStr] at h; simp at h

  | neg φ ih =>
      intro ψ h
      cases ψ with
      -- EXERCISE 2  Mirror image of Exercise 1.
      | atom q => rw [Fml.str_neg, Fml.str_atom, negStr] at h; simp at h

      | neg ψ =>
          rw [Fml.str_neg, Fml.str_neg, negStr, negStr] at h
          simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and,
            List.append_cancel_right_eq] at h
          rw [ih h]
      | bin d ψ₁ ψ₂ =>
          exfalso
          rw [Fml.str_neg, Fml.str_bin, negStr, binStr] at h
          simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
          obtain ⟨l', hl'⟩ := head_eq_of_append ψ₁.str_ne_nil h.symm
          exact str_ne_cons_neg ψ₁ l' hl'
  | bin c φ₁ φ₂ ih₁ ih₂ =>
      intro ψ h
      cases ψ with
      | atom q => rw [Fml.str_atom, Fml.str_bin, binStr] at h; simp at h
      | neg ψ =>
          exfalso
          rw [Fml.str_neg, Fml.str_bin, negStr, binStr] at h
          simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
          obtain ⟨l', hl'⟩ := head_eq_of_append φ₁.str_ne_nil h
          exact str_ne_cons_neg φ₁ l' hl'
      | bin d ψ₁ ψ₂ =>
          rw [Fml.str_bin, Fml.str_bin, binStr, binStr] at h
          simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
          have h₁ : φ₁.str = ψ₁.str := by
            rcases prefix_or_prefix_of_append_eq h with hp | hp
            · exact eq_of_str_prefix hp
            · exact (eq_of_str_prefix hp).symm
          rw [h₁] at h
          have h₂ := List.append_cancel_left h
          injection h₂ with hc htl
          injection hc with hcd
          have h₃ : φ₂.str = ψ₂.str := by
            simpa using htl
          rw [hcd, ih₁ h₁, ih₂ h₃]

/-! ## The notes' three-part phrasing

`str_injective` is the theorem, but it is stated about trees.  The next three
results restate it purely about strings and `Form P`, matching the three bullets
of the proof of **Theorem 1** one for one:
the `¬` case, the binary case, and the impossibility of a formula being read
both ways. -/

/-- **Theorem 1**, **Case 1.** A formula of the form
`(¬ φ)` determines its immediate subformula: `¬` applied to two formulas gives
the same string only if the two formulas are the same string.

(The membership hypotheses are those of the notes; the statement is in fact true
for arbitrary strings, since `negStr` is injective by plain string cancellation.
We route the proof through `str_injective` anyway, to match the notes.) -/
theorem negStr_inj {t t' : Str P} (ht : t ∈ Form P) (ht' : t' ∈ Form P)
    (h : negStr t = negStr t') : t = t' := by
  obtain ⟨φ, rfl⟩ := mem_form_iff_exists_fml.mp ht
  obtain ⟨ψ, rfl⟩ := mem_form_iff_exists_fml.mp ht'
  have := str_injective (a₁ := Fml.neg φ) (a₂ := Fml.neg ψ) h
  injection this with hp
  rw [hp]

/-- **Theorem 1**, **Case 2.** A formula of the form
`(φ₁ ∘ φ₂)` determines its primary connective *and both* immediate subformulas.
This is the substantive case: it is here that **Corollary 1** is needed,
to rule out `φ₁ ≺ ψ₁` and `ψ₁ ≺ φ₁`. -/
/- EXERCISE 4  **Theorem 1**, Case 2 — the same pattern as `negStr_inj`
   above, so read that proof first, then do it four times instead of twice.

   Replace each membership hypothesis by a tree, apply `str_injective` to the
   two `Fml.bin` trees, and take the resulting equality of trees apart with
   `injection`, which hands you all three components at once. -/
theorem binStr_inj {c d : Conn} {t₁ t₂ u₁ u₂ : Str P}
    (h₁ : t₁ ∈ Form P) (h₂ : t₂ ∈ Form P) (k₁ : u₁ ∈ Form P) (k₂ : u₂ ∈ Form P)
    (h : binStr c t₁ t₂ = binStr d u₁ u₂) : c = d ∧ t₁ = u₁ ∧ t₂ = u₂ := by
  obtain ⟨φ₁, rfl⟩ := mem_form_iff_exists_fml.mp h₁
  obtain ⟨φ₂, rfl⟩ := mem_form_iff_exists_fml.mp h₂
  obtain ⟨ψ₁, rfl⟩ := mem_form_iff_exists_fml.mp k₁
  obtain ⟨ψ₂, rfl⟩ := mem_form_iff_exists_fml.mp k₂
  have := str_injective (a₁ := Fml.bin c φ₁ φ₂) (a₂ := Fml.bin d ψ₁ ψ₂) h
  injection this with hc htl htr
  constructor
  · rw [hc]
  constructor
  · rw [htl]
  · rw [htr]

/-- **Theorem 1**, **mixed case.** No string is
simultaneously readable as `(¬ φ)` and as `(ψ₁ ∘ ψ₂)`; so the primary connective
of a non-atomic formula is unambiguously unary or binary.  The notes' reason:
otherwise `ψ₁` would have to begin with `¬`. -/
theorem negStr_ne_binStr {t u₁ u₂ : Str P} (ht : t ∈ Form P)
    (k₁ : u₁ ∈ Form P) (k₂ : u₂ ∈ Form P) (c : Conn) : negStr t ≠ binStr c u₁ u₂ := by
  obtain ⟨φ, rfl⟩ := mem_form_iff_exists_fml.mp ht
  obtain ⟨ψ₁, rfl⟩ := mem_form_iff_exists_fml.mp k₁
  obtain ⟨ψ₂, rfl⟩ := mem_form_iff_exists_fml.mp k₂
  intro h
  exact absurd (str_injective (a₁ := Fml.neg φ) (a₂ := Fml.bin c ψ₁ ψ₂) h) (by simp)

/-! ## Trees and formulas are in bijection -/

/-- **Syntax trees and well-formed formulas are the same thing.**

`range_str` (in `Syntax/Trees.lean`) says `Fml.str` is *onto* `Form P`;
`str_injective` — **Theorem 1** — says it is *one-to-one*.
Together: `Fml P ≃ Form P`.

This is the license for every later file (notably `Semantics/Basic.lean`) to
recurse over the tree instead of parsing the string: the recursion is
well-defined precisely because unique readability holds. -/
noncomputable def formEquiv : Fml P ≃ (Form P : Set (Str P)) :=
  (Equiv.ofInjective (Fml.str : Fml P → Str P) str_injective).trans
    (Equiv.setCongr range_str)

/-- The same statement as `formEquiv`, in `Set.BijOn` form. -/
theorem str_bijOn_form : Set.BijOn (Fml.str : Fml P → Str P) Set.univ (Form P) := by
  refine ⟨fun φ _ => φ.str_mem_form, fun a _ b _ h => str_injective h, ?_⟩
  intro s hs
  obtain ⟨φ, rfl⟩ := mem_form_iff_exists_fml.mp hs
  exact ⟨φ, Set.mem_univ _, rfl⟩

end PropLogic

-- make sure the required axiom audit is present
#print axioms PropLogic.str_injective
