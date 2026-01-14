# DD-Calculus: Formal Derivation of the Standard Model

[![Agda](https://img.shields.io/badge/Agda-2.6.4-blue)](https://wiki.portal.chalmers.se/agda)
[![Safe](https://img.shields.io/badge/--safe-✓-green)]()
[![Without-K](https://img.shields.io/badge/--without--K-✓-green)]()
[![Postulates](https://img.shields.io/badge/postulates-0-brightgreen)]()

**DD-Calculus** is a formal verification project that derives the structure of the Standard Model of particle physics from a single axiom: **Δ ≠ ∅** (distinction exists).

## The Complete Derivation Chain

```
                           Δ ≠ ∅
                       (Axiom: Distinction exists)
                              │
                              ▼
                    ┌─────────────────────┐
                    │  Triadic Closure    │
                    │  (ForcingTriad.agda)│
                    └─────────────────────┘
                              │
           ┌──────────────────┼──────────────────┐
           ▼                  ▼                  ▼
    ¬TriadicClosure(1)  ¬TriadicClosure(2)  TriadicClosure(3)
           │                  │                  │
           └──────────────────┴──────────────────┘
                              │
                              ▼
                        |Ω| = 3
                    (DERIVED, not postulated)
                              │
           ┌──────────────────┼──────────────────┐
           ▼                  ▼                  ▼
       Z₃ center         Dyad (2)           Monad (1)
           │                  │                  │
           ▼                  ▼                  ▼
        SU(3)              SU(2)              U(1)
       (color)           (weak)         (hypercharge)
           │                  │                  │
           └──────────────────┴──────────────────┘
                              │
                              ▼
                    SU(3) × SU(2) × U(1)
                   (Standard Model gauge group)
                              │
           ┌──────────────────┴──────────────────┐
           ▼                                     ▼
    3D Space (minimal)                    Linear Time
    (NoOmegaIn2D.agda)                (TimeOrdering.agda)
           │                                     │
           └──────────────────┬──────────────────┘
                              ▼
                       3+1 Spacetime
                    (Spacetime31.agda)
                              │
                              ▼
                    Standard Model Structure
```

## Key Theorems

### ForcingTriad: Why 3?

The central theorem proves that triadic closure **requires exactly 3 elements**:

```agda
-- Distinction/ForcingTriad.agda

record TriadicClosure (A : Set) : Set where
  field
    auto : Automorphism A
    order3 : (x : A) → iterate (fun auto) 3 x ≡ x
    not-id : Σ A (λ x → fun auto x ≢ x)
    not-order2 : Σ A (λ x → iterate (fun auto) 2 x ≢ x)

-- PROVEN:
no-triadic-one : ¬ (TriadicClosure One)   -- 1 element: only identity exists
no-triadic-two : ¬ (TriadicClosure Two)   -- 2 elements: order 2 (flip)
three-triadic  : TriadicClosure Three     -- 3 elements: order 3 ✓
```

### Gauge Group Uniqueness

```agda
-- DD/SU3Unique.agda
SU3-satisfies : TriadCompatibleGauge  -- SU(3) is unique for triads

-- DD/SU2Unique.agda  
SU2-satisfies : DyadCompatibleGauge   -- SU(2) is unique for dyads
```

### Spacetime Structure

```agda
-- DD/NoOmegaIn2D.agda
no-omega-in-2d : ¬ (Omega → 2D)       -- 3 colors need 3D

-- DD/TimeOrdering.agda
arrow-of-time : ArrowOfTime           -- Time is linear (ℕ with trichotomy)

-- DD/Spacetime31.agda
spacetime31 : Spacetime31             -- 3+1 dimensions derived
```

## Statistics

| Metric | Value |
|--------|-------|
| Modules | 97 |
| Lines of Code | 14,280 |
| Postulates | **0** |
| Intentional ⊤ | 2 |

The two intentional ⊤ placeholders are:
- `MassHierarchy.no-structural-selection` — Why top quark is heaviest (physical, not structural)
- `NeutrinoStructure.choice-is-dynamical` — Neutrino mixing pattern (dynamical, not topological)

## Building

```bash
# Requires Agda 2.6.4+
agda --safe --without-K src/DD/Index.agda
```

## Module Structure

```
src/
├── Core/
│   ├── Logic.agda          # Foundations (Σ, ≡, ⊥, etc.)
│   ├── Nat.agda            # Natural numbers
│   ├── Omega.agda          # Triadic structure {ω⁰, ω¹, ω²}
│   ├── OmegaTriadic.agda   # Bridge to ForcingTriad
│   └── Matrix.agda         # Parametric matrix algebra
│
├── Distinction/
│   ├── Core.agda           # Distinction operator
│   ├── ForcingTriad.agda   # WHY 3? (core theorem)
│   ├── ForcingT1.agda      # Closure axiom
│   └── ForcingT3.agda      # Stability
│
└── DD/
    ├── Index.agda          # Master module (compiles everything)
    ├── Triad.agda          # Triadic structure
    ├── SU3Unique.agda      # SU(3) uniqueness
    ├── SU2Unique.agda      # SU(2) uniqueness
    ├── Spacetime31.agda    # 3+1 dimensions
    ├── WeinbergAngle.agda  # sin²θ_W prediction
    └── ...                 # 80+ more modules
```

## The DD Philosophy

**Distinction Dynamics** is based on the principle that the structure of physical reality follows from the logic of distinction itself:

1. **Δ ≠ ∅**: Distinction exists (the only axiom)
2. **Closure**: The distinction operator is self-applicable
3. **Complex phase**: w³ = 1, w ≠ 1 (cube root of unity)
4. **Minimality**: Structures are as small as possible

From these principles, the entire gauge structure of the Standard Model emerges.

## Falsifiable Prediction (Patch-8)

**DD predicts: No asymptotic millicharged particles outside (1/3)ℤ.**

This is a *risky* prediction that can be killed by:
- Discovering a stable particle with Q = 10⁻³ e, Q = 1/2, or any Q ∉ (1/3)ℤ
- Confirmed kinetic mixing to non-lattice charges

See `REALITY_CHECK.md` for the full falsifiability analysis.

## Honesty Documents

| File | Purpose |
|------|---------|
| `REALITY_CHECK.md` | DD claims vs physical verification |
| `SEMANTIC_BRIDGE.md` | Code ↔ Physics mapping with explicit assumptions |
| `ASSUMPTIONS.md` | Full ledger of DD assumptions (A1–A10) |

These documents make DD a *conditional framework*, not a "theory of everything".

## References

- [PhilPapers: Distinction Dynamics](https://philpapers.org/) — ~50 preprints
- [GitHub Repository](https://github.com/leningradsky/dd-calculus)

## License

MIT
