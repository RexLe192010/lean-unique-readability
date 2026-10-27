/-
Copyright (c) 2026 Suguman Bansal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suguman Bansal
-/
/-
# Formula trees, and their rendering onto `Form`

`Syntax/Basic.lean` develops §2.1 entirely in terms of **strings**, because that
is what §2.2's argument is about: a formula is *a priori* nothing but a string
of symbols, and it takes a theorem (**Theorem 1** of the notes) to show
that a string determines its primary connective and immediate subformulas
(**Definition 3**).  A tree would assume that theorem rather than prove it.

This file adds the tree presentation and connects the two.  `Fml P` is the
abstract syntax tree, `Fml.str` renders it as a string with the notes'
parenthesization, and `range_str` says the trees render onto *exactly* `Form P`.

That is half of the correspondence.  The other half — that `Fml.str` is
**injective**, so a well-formed string comes from at most one tree — is unique
readability itself (**Theorem 1**), proved in `Syntax/UniqueReadability.lean`
from the parenthesis-counting lemmas **Lemma 2** and **Lemma 3**.

The split is deliberate.  Almost every later module needs the *tree* — semantics
recurses over it, and eager simplification, DPLL and the 3-colouring encoding all
build formulas with it — but almost none of them needs the parenthesis calculus.
Keeping the datatype here lets those modules import it without dragging in the
readability proof, and keeps visible the fact that the string development of
`Syntax/Basic.lean` never touches the tree.
-/
import PropLogic.Syntax.Basic

namespace PropLogic

universe u

variable {P : Type u}

/-- A propositional formula as an abstract syntax tree. -/
inductive Fml (P : Type u) where
  | atom (p : P)
  | neg (φ : Fml P)
  | bin (c : Conn) (φ₁ φ₂ : Fml P)
  deriving Repr

namespace Fml

/-- The string denoted by a formula tree, with the notes' parenthesization:
`p`, `(¬φ)`, `(φ₁ ∘ φ₂)`. -/
def str : Fml P → Str P
  | .atom p => [Sym.var p]
  | .neg φ => negStr φ.str
  | .bin c φ₁ φ₂ => binStr c φ₁.str φ₂.str

@[simp] theorem str_atom (p : P) : (Fml.atom p).str = [Sym.var p] := rfl

@[simp] theorem str_neg (φ : Fml P) : (Fml.neg φ).str = negStr φ.str := rfl

@[simp] theorem str_bin (c : Conn) (φ₁ φ₂ : Fml P) :
    (Fml.bin c φ₁ φ₂).str = binStr c φ₁.str φ₂.str := rfl

/-- The nesting depth of a formula: the index of the first stratum containing it. -/
def depth : Fml P → ℕ
  | .atom _ => 0
  | .neg φ => φ.depth + 1
  | .bin _ φ₁ φ₂ => max φ₁.depth φ₂.depth + 1

/-- No formula is the empty string. -/
@[simp] theorem str_ne_nil (φ : Fml P) : φ.str ≠ [] := by
  cases φ <;> simp

/-- A formula string sits in the stratum given by its depth. -/
theorem str_mem_stratum (φ : Fml P) : φ.str ∈ stratum P φ.depth := by
  induction φ with
  | atom p => exact ⟨p, rfl⟩
  | neg φ ih => exact Or.inl (Or.inr ⟨φ.str, ih, rfl⟩)
  | bin c φ₁ φ₂ ih₁ ih₂ =>
      exact Or.inr ⟨c, φ₁.str, stratum_mono (le_max_left _ _) ih₁,
        φ₂.str, stratum_mono (le_max_right _ _) ih₂, rfl⟩

theorem str_mem_form (φ : Fml P) : φ.str ∈ Form P :=
  mem_form_iff.mpr ⟨φ.depth, φ.str_mem_stratum⟩

end Fml

/-- Every string in a stratum is denoted by some tree. -/
theorem exists_fml_of_mem_stratum : ∀ (n : ℕ) {s : Str P}, s ∈ stratum P n → ∃ φ : Fml P, φ.str = s := by
  intro n
  induction n with
  | zero =>
      rintro s ⟨p, rfl⟩
      exact ⟨Fml.atom p, rfl⟩
  | succ n ih =>
      rintro s ((hs | ⟨t, ht, rfl⟩) | ⟨c, t₁, h₁, t₂, h₂, rfl⟩)
      · exact ih hs
      · obtain ⟨φ, rfl⟩ := ih ht
        exact ⟨Fml.neg φ, rfl⟩
      · obtain ⟨φ₁, rfl⟩ := ih h₁
        obtain ⟨φ₂, rfl⟩ := ih h₂
        exact ⟨Fml.bin c φ₁ φ₂, rfl⟩

/-- **The trees denote exactly the well-formed formulas.**

This is what licenses working with `Fml P` in place of `Form P` everywhere
downstream: nothing is lost (`⊇`) and nothing spurious is gained (`⊆`).  Together
with injectivity of `Fml.str` (`Syntax/UniqueReadability.lean`) it says `Fml P`
and `Form P` are in bijection. -/
theorem range_str : Set.range (Fml.str : Fml P → Str P) = Form P := by
  ext s
  constructor
  · rintro ⟨φ, rfl⟩
    exact φ.str_mem_form
  · intro hs
    obtain ⟨n, hn⟩ := mem_form_iff.mp hs
    obtain ⟨φ, hφ⟩ := exists_fml_of_mem_stratum n hn
    exact ⟨φ, hφ⟩

theorem mem_form_iff_exists_fml {s : Str P} : s ∈ Form P ↔ ∃ φ : Fml P, φ.str = s := by
  rw [← range_str]
  rfl

/-- The empty string is not a formula. Needed for the boundary case of
**Corollary 1**; see the discussion in `Syntax/UniqueReadability.lean`. -/
theorem nil_not_mem_form : ([] : Str P) ∉ Form P := by
  intro h
  obtain ⟨φ, hφ⟩ := mem_form_iff_exists_fml.mp h
  exact φ.str_ne_nil hφ

end PropLogic
