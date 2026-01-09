# arXiv Submission Metadata

## Paper Info

- **Title**: Type Theory from Distinction: Simply Typed Lambda Calculus as Structural Necessity
- **Authors**: Andrei Kozyrev
- **Primary Category**: cs.LO (Logic in Computer Science)
- **Cross-list**: math.LO (Logic)
- **License**: CC BY 4.0

## Abstract (150 words)

Modern mathematics and computer-verified proof systems are built on type theory, yet type theory itself is usually presented as an axiomatic starting point: types, equality, and functions are assumed rather than explained. We show that simply typed lambda calculus arises necessarily from a single meta-assumption: the existence of distinction. From this assumption we construct a minimal calculus in which types emerge as equivalence classes of indistinguishable elements, equality is induced by the absence of a distinguishing operation, and functions are exactly those mappings that preserve indistinguishability. Within this framework, the full soundness of simply typed lambda calculus is derived—not postulated—and a collapse theorem shows that if distinction is absent, all mathematical structure degenerates to a trivial system. The result is fully formalized and machine-verified in Agda, with no postulates or unproven assumptions.

## Comments

Machine-verified in Agda 2.6.4 with stdlib 2.0. Code available at [repository URL].

## MSC Classes

03B15 (Higher-order logic and type theory)
03B40 (Combinatory logic and lambda calculus)
03B70 (Logic in computer science)

## ACM Classes

F.4.1 (Mathematical Logic - Lambda calculus and related systems)
D.3.1 (Formal Definitions and Theory)

## Files to Submit

1. dd-calculus-paper.tex (source)
2. dd-calculus-paper.pdf (compiled)
3. src/ (Agda code as ancillary files)

## Submission Checklist

- [ ] Create arXiv account (if not exists)
- [ ] Upload .tex source
- [ ] Upload Agda code as ancillary
- [ ] Set metadata
- [ ] Preview and submit
- [ ] Wait for moderation (usually 1-2 days)
