# Unique readability in Lean 4

This repository formalizes unique readability for fully parenthesized propositional formulas: every well-formed sequence of symbols represents exactly one syntax tree. For example, `((p ∧ q) → r)` has implication at its root, with `(p ∧ q)` and `r` as its two subformulas.

The development separates formula strings from syntax trees. `range_str` shows that every well-formed string has a representing tree; `str_injective` shows that this tree is unique. `formEquiv` combines these results. The proof uses parenthesis balance, properties of prefixes, and structural induction.

## Scope and attribution

The foundational development, definitions, theorem statements, and overall proof strategy are by Professor Suguman Bansal. Xinyi (Rex) Le completed six designated proof obligations in `UniqueReadability.lean` and analyzed their role in the proof. The six numbered markers in the source identify these obligations; the surrounding development is inherited material.

This repository contains the completed syntax and unique-readability development. It does not implement an executable parser, formula evaluation, SAT solving, or resolution. Historical source comments refer to a broader set of notes; those notes are not included here.

## Requirements and build

Install Lean's `elan` toolchain manager and Git. The `lean-toolchain` file selects Lean 4.15.0. Mathlib is specified at v4.15.0; `lake-manifest.json` records the resolved dependency commits. Keep the manifest to reproduce those versions.

From the repository root:

```sh
lake exe cache get
lake build
lake env lean PropLogic/Syntax/UniqueReadability.lean
```

The default build imports all three syntax modules, including the unique-readability theorem. The explicit equivalent build target is:

```sh
lake build PropLogic.Syntax.UniqueReadability
```

The final command in `UniqueReadability.lean` audits the theorem's axioms. Expected output:

```text
'PropLogic.str_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
```

In particular, this list contains no `sorryAx` placeholder-proof dependency. The proof is checked relative to the listed foundational axioms. First-time dependency setup requires network access; generated files and downloaded dependencies in `.lake/` are excluded from Git.

## Files

| File | Purpose |
| --- | --- |
| `PropLogic/Syntax/Basic.lean` | Symbol alphabet and well-formed formula strings |
| `PropLogic/Syntax/Trees.lean` | Formula trees, rendering, and existence of a tree for each well-formed string |
| `PropLogic/Syntax/UniqueReadability.lean` | Parenthesis and prefix lemmas, rendering injectivity, and six completed proof obligations |
| `PropLogic.lean` | Entry point importing the complete development in this repository |
| `CHAPTER-MAPPING.md` | Historical correspondence with the original notes; includes references to material outside this repository |

## License

Apache License 2.0; see [LICENSE](LICENSE). The original source headers attribute copyright to Suguman Bansal (2026). Those notices are preserved. Dependencies retain their own licenses.
