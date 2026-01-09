# DD-Calculus v0.1

## Distinction-Based Foundations of Simply Typed Lambda Calculus (STLC)

---

## 0. Purpose and Scope

This document specifies **DD-calculus v0.1**, a minimal formal system whose sole meta-assumption is the existence of distinction.
From this assumption, we derive the core structure of **Simply Typed Lambda Calculus (STLC)**: types, equality, functions, and composition.

This system is intentionally minimal:

* no dependent types (Π, Σ)
* no inductive types
* no universes
* no built-in logic

The goal is not expressiveness, but **forced emergence**.

---

## 1. Meta-Axiom

### A0 (Distinction)

There exists at least one distinction.

Informally: not all entities are indistinguishable.
Formally:
```
∃ x,y. x ≁ y
```

No further axioms about logic, types, or equality are assumed.

---

## 2. Primitive Data

### 2.1 Carrier of Entities

Let U be a nonempty collection of entities.

> U is **not** a type in the sense of type theory.
> It is a pre-theoretic domain of potential distinguishables.

---

### 2.2 Distinguishers

Let 𝒟 be a collection of distinguishers.

Each distinguisher d ∈ 𝒟 is an observation:
```
d : U → L_d
```
where L_d is a set of labels.

Interpretation: a distinguisher assigns an observable outcome to each entity.

---

## 3. Distinction and Indistinguishability

### 3.1 Distinction

Two entities are **distinguishable** if some distinguisher separates them:
```
x # y  :⟺  ∃ d ∈ 𝒟. d(x) ≠ d(y)
```

### 3.2 Indistinguishability

Two entities are **indistinguishable** if no distinguisher separates them:
```
x ~ y  :⟺  ¬(x # y)
```

---

## 4. Structural Axioms on Distinguishers

To make mathematics possible (i.e. stable under reasoning), we impose the following **coherence conditions**.

### A1 (Equivalence)

Indistinguishability ~ is an equivalence relation:

* Reflexive: x ~ x
* Symmetric: x ~ y ⟹ y ~ x
* Transitive: x ~ y ∧ y ~ z ⟹ x ~ z

> This is not an axiom of equality — it is a requirement that *non-distinction behaves coherently*.

---

### A2 (Conjunction of Distinguishers)

For any d₁, d₂ ∈ 𝒟, there exists a distinguisher d such that:
```
d(x) = d(y)  ⟹  d₁(x) = d₁(y) ∧ d₂(x) = d₂(y)
```

Interpretation: distinguishers can be combined.

---

## 5. Derived Notions

### 5.1 Types

A **type** is an equivalence class under indistinguishability:
```
Type_Δ := U / ~
```

Elements of a type are indistinguishable entities.

---

### 5.2 Equality

Equality is **not primitive**.

For representatives x, y ∈ U:
```
[x] =_Δ [y]  :⟺  x ~ y
```

Reflexivity (`refl`) follows immediately from A1.

---

## 6. Morphisms (Functions)

### 6.1 Δ-Morphisms

A function f : U → U is **Δ-compatible** if:
```
x ~ y  ⟹  f(x) ~ f(y)
```

Interpretation: functions cannot create distinctions from indistinguishable inputs.

---

### 6.2 Induced Functions on Types

Any Δ-morphism induces a function on types:
```
f̄ : U/~ → U/~,    f̄([x]) := [f(x)]
```

This is well-defined by Δ-compatibility.

---

## 7. Composition and Identity

### 7.1 Identity

The identity function id(x) = x is Δ-compatible.

---

### 7.2 Composition

If f, g are Δ-compatible, then so is g ∘ f.

---

### Theorem 7.3 (Category of Types)

Types U/~ and Δ-morphisms form a category **DD₀**.

---

## 8. STLC Interpretation

### 8.1 Contexts

A context is a finite product of types in **DD₀**.

---

### 8.2 Terms

A term Γ ⊢ t : A is interpreted as a Δ-morphism:
```
⟦t⟧ : ⟦Γ⟧ → A
```

---

### 8.3 Lambda Abstraction

Lambda abstraction corresponds to currying of Δ-morphisms.

---

### 8.4 Application

Application corresponds to evaluation.

---

### Theorem 8.5 (Soundness of STLC)

Simply Typed Lambda Calculus is sound with respect to DD-calculus semantics.

---

## 9. Collapse Theorem

### Theorem 9.1 (Collapse)

If 𝒟 = ∅, then:

* all entities are indistinguishable
* there is exactly one type
* all functions are equal
* no nontrivial term can be distinguished

Hence, **nontrivial mathematics is impossible**.

---

## 10. Interpretation

* Type theory is **not assumed**
* Equality is **not primitive**
* Functions are **forced by preservation of indistinguishability**
* STLC emerges as the minimal stable structure under distinction

---

## 11. Status

* Version: **v0.1**
* Target: STLC (no Π/Σ)
* Next version: **v0.2 — dependent types via fibrations**
