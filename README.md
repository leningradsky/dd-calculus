# DD-Calculus v0.1

**Simply Typed Lambda Calculus derived from the existence of distinction.**

[![Agda](https://img.shields.io/badge/Agda-2.6.4-blue)](https://wiki.portal.chalmers.se/agda)
[![stdlib](https://img.shields.io/badge/stdlib-2.0-green)](https://github.com/agda/agda-stdlib)
[![Postulates](https://img.shields.io/badge/postulates-0-brightgreen)]()

## What is this?

We show that simply typed lambda calculus arises necessarily from a single meta-assumption: **the existence of distinction (Δ ≠ ∅)**. 

From this assumption we construct a minimal calculus in which:
- **Types** emerge as equivalence classes of indistinguishable elements
- **Equality** is induced by the absence of a distinguishing operation  
- **Functions** are exactly those mappings that preserve indistinguishability

The full soundness of STLC is *derived*—not postulated—and a collapse theorem shows that if distinction is absent, all mathematical structure degenerates to a trivial system.

This establishes type theory not as a conventional choice of axioms, but as a structure **forced** by the mere possibility of making distinctions.

## Key Results

| Theorem | Statement |
|---------|-----------|
| **Soundness** | Every well-typed STLC term denotes a Δ-morphism |
| **Collapse** | D = ∅ ⟹ all types collapse to one point |
| **Category** | Types and Δ-morphisms form a category DD₀ |

## Structure

```
src/
├── DDCalculus.agda          # Main module
└── Distinction/
    ├── Core.agda            # U, D, eval, #, ~
    ├── Axioms.agda          # A1 (equivalence), A2 (conjunction)
    ├── Types.agda           # Types as U/~
    ├── Morphisms.agda       # Δ-morphisms
    ├── Category.agda        # DD₀ category laws
    ├── Collapse.agda        # Theorem: D=∅ ⟹ trivial
    ├── STLC.agda            # STLC syntax
    └── Soundness.agda       # ★ Full soundness proof
```

## Build

```bash
# Requires Agda 2.6.4+ and stdlib 2.0+
cd src
agda DDCalculus.agda
```

Expected output: no errors, exit code 0.

## Statistics

- **Total lines**: ~900
- **Postulates**: 0
- **Sorry**: 0
- **Axioms beyond Δ≠∅**: 0

## Formal Specification

See [SPEC.md](SPEC.md) for the complete formal specification of DD-calculus.

## Citation

```bibtex
@software{dd-calculus-v01,
  author = {Kozyrev, Andrei},
  title = {DD-Calculus: Type Theory from Distinction},
  version = {0.1},
  year = {2026},
  url = {https://github.com/...}
}
```

## License

MIT
