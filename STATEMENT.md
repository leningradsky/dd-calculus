# DD-Calculus v0.1 — Core Statement

## Three-paragraph formulation (canonical)

**Paragraph 1 — the problem**

Modern mathematics and computer-verified proof systems are built on type theory, yet type theory itself is usually presented as an axiomatic starting point: types, equality, and functions are assumed rather than explained. This leaves a foundational gap: why is type theory a legitimate framework at all, and why does it succeed so uniformly across logic, computation, and formal mathematics? Standard answers appeal to convenience or consistency, but do not explain why these structures are forced rather than chosen.

**Paragraph 2 — the result**

We show that simply typed lambda calculus arises necessarily from a single meta-assumption: the existence of distinction (Δ ≠ ∅). From this assumption we construct a minimal calculus of distinctions in which types emerge as equivalence classes of indistinguishable elements, equality is induced by the absence of a distinguishing operation, and functions are exactly those mappings that preserve indistinguishability. Within this framework, the full soundness of simply typed lambda calculus is derived—not postulated—and a collapse theorem shows that if distinction is absent, all mathematical structure degenerates to a trivial system.

**Paragraph 3 — the significance**

This establishes type theory not as a conventional choice of axioms, but as a structure forced by the mere possibility of making distinctions. The result is fully formalized and machine-verified in Agda, with no postulates or unproven assumptions. Consequently, type theory appears as a necessary foundation for formal reasoning rather than a discretionary one, shifting the foundations of mathematics from axiomatic selection to structural inevitability.

---

## Usage

- **Abstract**: use as-is or compress to 150 words
- **README**: use Paragraph 2 + 3
- **Verbal pitch**: memorize Paragraph 2, drop technical details
- **Skeptic response**: "show me where you deny that distinction exists"
