/-
Copyright (c) 2026 Suguman Bansal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suguman Bansal
-/
/-
# Syntax of propositional logic

This file formalizes §2.1 ("Syntax") of the notes: the alphabet, the two
definitions of the set `Form` of well-formed formulas, and their equivalence.

## The two definitions, and why we keep both

The notes give `Form` twice.

* **Definition 1** (p. 6) is *non-constructive*: `Form` is the **smallest** set
  of strings containing every proposition and closed under the formation rules.
  That is `FormInter` below, an intersection of all closed sets.
* **Definition 2** (p. 7) is *constructive*: `Form' = ⋃ᵢ Formᵢ` for an explicit
  chain of strata.  That is `Form` below.

**Claim 1** (p. 7) says the two agree; that is `formInter_eq_form`.  Both are
genuinely needed downstream: the strata carry the induction principle every
later proof uses, while the "smallest closed set" formulation is what
`form_unique` needs to say `Form` is well-defined at all — **Lemma 1** (p. 7).
Numbered results and page numbers throughout this file refer to the course
notes (`main.pdf`).

## Strings versus trees

Everything in this file is about **strings** — elements of `List (Sym P)` — and
that is deliberate.  The whole point of §2.1's unique-readability development is
that a formula is *a priori* nothing but a string of symbols, and that it takes a
theorem (**Theorem 1**, p. 11, in `Syntax/UniqueReadability.lean`) to show a
string determines its primary connective and immediate subformulas.  Modelling formulas directly as an
inductive tree would *assume* unique readability rather than prove it, which
would silently skip the section.

So we carry both, and connect them, but in separate files.  `Syntax/Trees.lean`
introduces the inductive tree `Fml P`, its rendering `Fml.str`, and `range_str`,
which says the trees render onto exactly `Form`.  Unique readability is then the
statement that `Fml.str` is *injective* — a string comes from at most one tree —
which `Syntax/UniqueReadability.lean` proves from the parenthesis-counting
lemmas, exactly as the notes do.  Semantics (`Semantics/Basic.lean`) then
recurses over the tree, which is legitimate precisely because of that
injectivity.

Nothing below this docstring mentions the tree: the two definitions of `Form`
and their equivalence are established for strings alone.
-/
import Arlib.Prelude
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Lattice

namespace PropLogic

universe u

variable {P : Type u}

/-! ## The alphabet -/

/-- The binary connectives of the notes, jointly denoted `∘`: `∧`, `∨`, `→`. -/
inductive Conn where
  | and
  | or
  | imp
  deriving DecidableEq, Repr

/-- A symbol of the alphabet of propositional logic: a proposition from `P`, the
unary connective `¬`, a binary connective, or a parenthesis. -/
inductive Sym (P : Type u) where
  | var (p : P)
  | neg
  | conn (c : Conn)
  | lpar
  | rpar
  deriving DecidableEq

/-- A string over the alphabet. Formulas are particular strings. -/
abbrev Str (P : Type u) := List (Sym P)

/-- The string `(¬ t)`.

Parenthesized right-associatively (`[lpar] ++ ([neg] ++ (t ++ [rpar]))`) rather
than in the left-associated normal form of `++`, because every proof about
prefixes peels symbols off the *front*, and this is the shape that makes
`prefix_append_cases` apply directly. -/
def negStr (t : Str P) : Str P :=
  [Sym.lpar] ++ ([Sym.neg] ++ (t ++ [Sym.rpar]))

/-- The string `(t₁ ∘ t₂)` for a binary connective `∘`. Right-associated for the
same reason as `negStr`. -/
def binStr (c : Conn) (t₁ t₂ : Str P) : Str P :=
  [Sym.lpar] ++ (t₁ ++ ([Sym.conn c] ++ (t₂ ++ [Sym.rpar])))

@[simp] theorem negStr_ne_nil (t : Str P) : negStr t ≠ [] := by simp [negStr]

@[simp] theorem binStr_ne_nil (c : Conn) (t₁ t₂ : Str P) : binStr c t₁ t₂ ≠ [] := by
  simp [binStr]

/-! ## The constructive definition: the strata `Formᵢ` -/

/-- The strata of **Definition 2** (p. 7):

`Form₀ = P`, and `Formᵢ₊₁` adds one layer of `¬` and one layer of binary
connectives on top of `Formᵢ` (retaining `Formᵢ` itself). -/
def stratum (P : Type u) : ℕ → Set (Str P)
  | 0 => {s | ∃ p : P, s = [Sym.var p]}
  | n + 1 =>
      stratum P n
        ∪ {s | ∃ t ∈ stratum P n, s = negStr t}
        ∪ {s | ∃ c : Conn, ∃ t₁ ∈ stratum P n, ∃ t₂ ∈ stratum P n, s = binStr c t₁ t₂}

/-- `Form = ⋃ᵢ Formᵢ`, the constructive definition `Form'` of the notes.

This is the definition all later files use, because it is the one that supplies
an induction principle. `formInter_eq_form` identifies it with the notes' primary
(non-constructive) definition. -/
def Form (P : Type u) : Set (Str P) := ⋃ n, stratum P n

theorem mem_form_iff {s : Str P} : s ∈ Form P ↔ ∃ n, s ∈ stratum P n := by
  simp [Form]

theorem subset_stratum_succ (n : ℕ) : stratum P n ⊆ stratum P (n + 1) := by
  intro s hs
  exact Or.inl (Or.inl hs)

/-- The strata are increasing. -/
theorem stratum_mono {m n : ℕ} (h : m ≤ n) : stratum P m ⊆ stratum P n := by
  induction n with
  | zero =>
      obtain rfl : m = 0 := Nat.le_zero.mp h
      exact subset_rfl
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · exact (ih (Nat.lt_succ_iff.mp hlt)).trans (subset_stratum_succ n)
      · have : m = n + 1 := le_antisymm h hge
        subst this
        exact subset_rfl

theorem mem_stratum_of_mem_form {s : Str P} (h : s ∈ Form P) : ∃ n, s ∈ stratum P n :=
  mem_form_iff.mp h

/-! ## The non-constructive definition: the smallest closed set -/

/-- `S` contains every proposition and is closed under the formation rules —
the two bullets of **Definition 1** (p. 6). -/
structure IsClosed (S : Set (Str P)) : Prop where
  atom : ∀ p : P, [Sym.var p] ∈ S
  neg : ∀ t ∈ S, negStr t ∈ S
  bin : ∀ (c : Conn), ∀ t₁ ∈ S, ∀ t₂ ∈ S, binStr c t₁ t₂ ∈ S

/-- The notes' `Form' = ⋂ Q`, the intersection of every set containing the
propositions and satisfying closure. This is the witness used in the proof of
**Lemma 1** (p. 7) to show a smallest such set exists. -/
def FormInter (P : Type u) : Set (Str P) := ⋂₀ {S : Set (Str P) | IsClosed S}

theorem mem_formInter_iff {s : Str P} :
    s ∈ FormInter P ↔ ∀ S : Set (Str P), IsClosed S → s ∈ S := by
  simp [FormInter, Set.mem_sInter]

/-- `FormInter` is itself closed — the second bullet of **Lemma 1** (p. 7). -/
theorem isClosed_formInter : IsClosed (FormInter (P := P)) where
  atom p := mem_formInter_iff.mpr fun _ hS => hS.atom p
  neg t ht := mem_formInter_iff.mpr fun S hS => hS.neg t (mem_formInter_iff.mp ht S hS)
  bin c t₁ h₁ t₂ h₂ :=
    mem_formInter_iff.mpr fun S hS =>
      hS.bin c t₁ (mem_formInter_iff.mp h₁ S hS) t₂ (mem_formInter_iff.mp h₂ S hS)

/-- `FormInter` is contained in every closed set — the third bullet of
**Lemma 1** (p. 7) ("smallest"). -/
theorem formInter_subset {S : Set (Str P)} (hS : IsClosed S) : FormInter P ⊆ S :=
  fun _ hs => mem_formInter_iff.mp hs S hS

/-! ## The two definitions agree -/

/-- `Form` (constructive) is closed. This is the first two bullets of the proof
of **Claim 1** (p. 7). -/
theorem isClosed_form : IsClosed (Form (P := P)) where
  atom p := mem_form_iff.mpr ⟨0, ⟨p, rfl⟩⟩
  neg t ht := by
    obtain ⟨n, hn⟩ := mem_form_iff.mp ht
    exact mem_form_iff.mpr ⟨n + 1, Or.inl (Or.inr ⟨t, hn, rfl⟩)⟩
  bin c t₁ h₁ t₂ h₂ := by
    obtain ⟨n₁, hn₁⟩ := mem_form_iff.mp h₁
    obtain ⟨n₂, hn₂⟩ := mem_form_iff.mp h₂
    refine mem_form_iff.mpr ⟨max n₁ n₂ + 1, Or.inr ⟨c, t₁, ?_, t₂, ?_, rfl⟩⟩
    · exact stratum_mono (le_max_left _ _) hn₁
    · exact stratum_mono (le_max_right _ _) hn₂

/-- Every stratum lands inside any closed set. This is the induction in the third
bullet of the proof of **Claim 1** (p. 7). -/
theorem stratum_subset_of_isClosed {S : Set (Str P)} (hS : IsClosed S) :
    ∀ n, stratum P n ⊆ S := by
  intro n
  induction n with
  | zero =>
      rintro s ⟨p, rfl⟩
      exact hS.atom p
  | succ n ih =>
      rintro s (( hs | ⟨t, ht, rfl⟩) | ⟨c, t₁, h₁, t₂, h₂, rfl⟩)
      · exact ih hs
      · exact hS.neg t (ih ht)
      · exact hS.bin c t₁ (ih h₁) t₂ (ih h₂)

/-- `Form` is contained in every closed set, i.e. it really is the *smallest*
one. -/
theorem form_subset_of_isClosed {S : Set (Str P)} (hS : IsClosed S) : Form P ⊆ S := by
  rintro s hs
  obtain ⟨n, hn⟩ := mem_form_iff.mp hs
  exact stratum_subset_of_isClosed hS n hn

/-- **Claim 1** (p. 7): the constructive and the non-constructive definitions
of `Form` describe the same set. -/
theorem formInter_eq_form : FormInter P = Form P :=
  Set.Subset.antisymm (formInter_subset isClosed_form) (form_subset_of_isClosed isClosed_formInter)

/-- **Lemma 1** (p. 7): `Form` is well defined — a smallest set
containing the propositions and closed under the formation rules exists, and it
is unique.  Existence is `isClosed_form` together with `form_subset_of_isClosed`;
this statement is the uniqueness half. -/
theorem form_unique (S : Set (Str P)) (hcl : IsClosed S)
    (hmin : ∀ T : Set (Str P), IsClosed T → S ⊆ T) : S = Form P :=
  Set.Subset.antisymm (hmin _ isClosed_form) (form_subset_of_isClosed hcl)

end PropLogic
