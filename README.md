# DD-Calculus

**Type theory and mathematical structure derived from the existence of distinction.**

[![Agda](https://img.shields.io/badge/Agda-2.6.4-blue)](https://wiki.portal.chalmers.se/agda)
[![stdlib](https://img.shields.io/badge/stdlib-2.0-green)](https://github.com/agda/agda-stdlib)
[![Postulates](https://img.shields.io/badge/postulates-0-brightgreen)]()

---

## The Core Claim

From a single meta-assumption — **the existence of distinction (Δ ≠ ∅)** — we derive:

1. **v0.1**: Simply typed lambda calculus as structural necessity
2. **v0.3**: The forcing theorems that make stable knowledge possible

This establishes mathematics not as a choice of axioms, but as structure **forced** by the possibility of making distinctions.

---

## v0.1: STLC from Distinction

Simply typed lambda calculus emerges necessarily:

- **Types** = equivalence classes of indistinguishable elements
- **Equality** = absence of distinguishing operation
- **Functions** = maps preserving indistinguishability

| Result | Statement |
|--------|-----------|
| **Soundness** | Every well-typed term denotes a Δ-morphism |
| **Collapse** | D = ∅ ⟹ all types collapse to one point |
| **Category** | Types + Δ-morphisms form category DD₀ |

**Files**: `src/Distinction/{Core,Axioms,Types,Morphisms,Category,Collapse,STLC,Soundness}.agda`

---

## v0.3: The Forcing Trilogy

When distinction exists, what makes stable knowledge possible?

Three forcing theorems cut the knife-edge:

### T1: Closure Forced by Stability

> If you want universal stabilization of equivalence classes, your observation language must be **closed under composition**.

Without closure: any "stable" classification can be shattered by a composite distinguisher you haven't yet applied.

### T2: Induction Forced by Iteration

> If you have an iterable refinement process, you necessarily have **ℕ-structure and induction**.

This is not "assuming ℕ as foundation" — it's showing that any system with refinement trajectories forces the emergence of natural numbers as the unique indexing structure for finite iteration.

### T3: Collapse-3 (No Stability ⟹ No Knowledge)

> If refinement perpetually splits every equivalence class (Drift), then **no nontrivial stable classifier exists**.

Any "knowledge" that respects all refinement steps must be constant — science collapses into infinite revision.

### The Knife-Edge

```
EITHER:
  Closed language (T1) + Induction (T2) → Stable objects exist
  
OR:
  Perpetual drift → Epistemic collapse (T3)
```

Stable ontology is possible **if and only if** the observation language has the right algebraic structure.

**Files**: `src/Distinction/{DistSystem,Equivalence,Stabilization,ForcingT1,ForcingT2,ForcingT3}.agda`

---

## Build

```bash
# Requires Agda 2.6.4+ and stdlib 2.0+
cd src
agda DDCalculus.agda
```

Expected: no errors, exit code 0.

## Statistics

| Version | Lines | Postulates | Sorry |
|---------|-------|------------|-------|
| v0.1 | ~900 | 0 | 0 |
| v0.3 | ~800 | 0 | 0 |

## Specifications

- [SPEC.md](SPEC.md) — v0.1 formal specification
- [SPEC-v0.3.md](SPEC-v0.3.md) — v0.3 forcing theorems

## Citation

```bibtex
@software{dd-calculus,
  author = {Kozyrev, Andrei},
  title = {DD-Calculus: Type Theory from Distinction},
  year = {2026},
  url = {https://github.com/leningradsky/dd-calculus}
}
```

## License

MIT
