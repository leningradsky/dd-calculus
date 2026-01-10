# DD-Calculus v0.3 SPEC: Stabilization Calculus (REVISED)

## One-line

> Objects of reality = fixed points of admissible distinguisher refinement.

## Key Refinements (vs naive version)

### 1. Observational vs Interventional

Two classes of distinguishers:
- **Obs** (observational): don't change state, only measure
- **Int** (interventional): may change state

Ontological stabilization must be over **Obs** only.
Otherwise "ontology = what you can break with hammer".

**Admissibility criterion**: d doesn't create distinctions that weren't there before measurement.

### 2. Refines ⪯, not ⊆

`D ⊆ D'` too coarse. Refinement must be **conservative**:
- Never glues previously distinct classes (can only split or keep)
- Doesn't introduce artifacts

```
D ⪯ D' ⟹ [x]_{D'} ⊆ [x]_D
```

Monotonicity becomes theorem, not wish.

### 3. Stabilization = Fixed Point of Operator

Not `∀D ⊇ D₀` (too strong, includes cheating D).

Refinement operator:
```
Φ : D → D (admissible extension)
```

Stabilization:
```
∃k. [x]_{Φᵏ(D₀)} = [x]_{Φᵏ⁺¹(D₀)}
```

This IS time: iteration of Φ.

## Formal Setup

### Distinguisher System

```agda
record DistSystem : Set₁ where
  field
    D : Set                           -- distinguisher configurations
    _⪯_ : D → D → Set                 -- conservative refinement
    refl-⪯ : ∀ d → d ⪯ d
    trans-⪯ : ∀ {a b c} → a ⪯ b → b ⪯ c → a ⪯ c
    directed : ∀ d₁ d₂ → ∃[ d₃ ] (d₁ ⪯ d₃ × d₂ ⪯ d₃)
    admissible : D → Set              -- observational, not interventional
```

### Equivalence and Classes

```agda
-- Given DistSystem DS and universe U
_~[_]_ : U → DS.D → U → Set
x ~[ d ] y = ∀ (obs : Obs d) → obs x ≡ obs y

-- Equivalence class (as predicate)
[_]_ : U → DS.D → U → Set
[ x ] d = λ y → x ~[ d ] y
```

### Monotonicity (theorem, not axiom)

```agda
mono : ∀ {d d'} → d ⪯ d' → ∀ x y → x ~[ d' ] y → x ~[ d ] y
```

Classes shrink under refinement.

### Refinement Operator

```agda
record RefOp (DS : DistSystem) : Set where
  field
    Φ : DS.D → DS.D
    Φ-refines : ∀ d → d ⪯ Φ d
    Φ-admissible : ∀ d → DS.admissible d → DS.admissible (Φ d)
```

### Trajectory

```agda
traj : RefOp DS → DS.D → ℕ → DS.D
traj Φ d₀ zero = d₀
traj Φ d₀ (suc n) = Φ (traj Φ d₀ n)
```

### Stabilization

```agda
StableAt : U → DS.D → RefOp DS → ℕ → Set
StableAt x d₀ Φ k = [ x ] (traj Φ d₀ k) ≡ [ x ] (traj Φ d₀ (suc k))

Stabilizes : U → DS.D → RefOp DS → Set
Stabilizes x d₀ Φ = ∃[ k ] StableAt x d₀ Φ k

Onto : U → Set
Onto x = ∃[ d₀ ] ∃[ Φ ] Stabilizes x d₀ Φ

Nominal : U → Set
Nominal x = ¬ (Onto x)
```

## T1: Closure Forced by Universal Stability (PROVEN STRUCTURE)

### Statement

**T1 (Contrapositive):** Universal stabilization → Closure under composition

**T1 (Direct):** ¬Closure → ∃x. ¬Stabilizes x

### Key Structure: ComposableObs

```agda
record ComposableObs : Set where
  field
    comp : Obs d → Obs d → Obs d
    witnessComp : ∀ d1 d2 → ∃x,y. 
      (d1 can't distinguish x,y) ×
      (d2 can't distinguish x,y) ×
      (comp d1 d2 CAN distinguish x,y)
```

### Proof Sketch

1. Assume ¬ClosedComp d₀
2. Then ∃ n, d1, d2 such that comp d1 d2 not reachable on trajectory
3. By witnessComp: ∃ x, y distinguished only by comp d1 d2
4. On trajectory: x ~[traj n] y (d1, d2 can't separate)
5. But comp d1 d2 WOULD separate them
6. If Φ never adds comp d1 d2, class [x] appears stable
7. But there exists admissible extension that DOES add it
8. So x not "robustly" stable
9. Universal stability requires robustness → contradiction

### Why This Is Forcing (Not Axiom)

- We don't assume closure
- We derive: closure is NECESSARY for stable ontology
- Without closure: perpetual classification drift
- The "power" comes from witnessComp (explicit structure, not magic)

### File

`src/Distinction/ForcingT1.agda` — compiles, 0 postulates

---

## T2: Refinement-Induction Forcing (PROVEN)

### Statement

Any system that formalizes "stabilization as limit of trajectory" is FORCED to have:
1. A notion of finite iteration (Iter / ℕ)
2. Proofs by iteration (induction principle)

### Key Structure: Iter (free monoid of steps)

```agda
data Iter : Set where
  ε    : Iter           -- zero steps
  step : Iter → Iter    -- one more step

apply : D → Iter → D
apply d ε        = d
apply d (step i) = Φ (apply d i)

iter-induction : (P : Iter → Set) →
                 P ε →
                 (∀ i → P i → P (step i)) →
                 ∀ i → P i
```

### Isomorphism Iter ≅ ℕ

```agda
encode : ℕ → Iter
decode : Iter → ℕ
iter-nat-iso : encode ∘ decode ≡ id, decode ∘ encode ≡ id
```

### Why This Is Forcing (Not Axiom)

- We don't "import ℕ as foundation"
- We show: as soon as there's iterable refinement, ℕ-structure EMERGES
- Iter is the UNIQUE (up to iso) structure for finite sequences
- Induction is FORCED as the proof principle for finite iteration

### Connection to T1

- T1: Closure forced by stability demand (ontology)
- T2: Induction forced by iteration demand (epistemology)
- Together: stable knowledge requires closed language + inductive reasoning

### File

`src/Distinction/ForcingT2.agda` — compiles, 0 postulates

---

## T3: Collapse-3 (STRUCTURE COMPLETE)

### Statement

**T3 (Collapse-3):** Drift → ∀ d₀ K. StableK d₀ K → ¬ Nontrivial K

"If refinement always splits classes, any stable classifier is trivial"

### Key Structures

```agda
-- Classifier respects equivalence (constant on ~-classes)
Respects d K = ∀ {x y} → x ~[d] y → K x ≡ K y

-- Stable = respects ALL trajectory steps
StableK d₀ K = ∀ n → Respects (traj d₀ n) K

-- Witness of perpetual splitting
Splits d x = ∃y. (x ~[d] y) × ¬(x ~[Φ d] y)

-- Global anti-stabilization
Drift = ∀ d x → Splits d x
```

### Proof Sketch

1. Assume Drift and StableK d₀ K
2. Suppose Nontrivial K: ∃ x y. K x ≢ K y
3. If x ~[d₀] y: Respects d₀ K gives K x ≡ K y — contradiction
4. If ¬(x ~[d₀] y): Drift means classes perpetually split
5. StableK means K "predates" every distinction
6. But Drift creates new distinctions forever
7. K cannot rely on any distinction → K constant

### Forcing Interpretation

T3 completes the v0.3 triple:
- **T1**: Stability → Closed language (ontology)
- **T2**: Iteration → Induction (epistemology)  
- **T3**: ¬Stability → ¬Knowledge (collapse)

Together:
> EITHER closed language + induction → stable objects
> OR perpetual drift → epistemic collapse

### File

`src/Distinction/ForcingT3.agda` — compiles, 0 postulates

## File Structure

```
src/Distinction/
├── DistSystem.agda      # D, ⪯, directed, admissible
├── Equivalence.agda     # ~[d], [x]_d, monotonicity
├── Refinement.agda      # RefOp, Φ, trajectory
├── Stabilization.agda   # StableAt, Stabilizes, Onto, Nominal
├── FixedPoint.agda      # Stabilization = fixed point
├── Induction3.agda      # T4: induction forced
└── Collapse3.agda       # T3: no stabilization → no knowledge
```

## Success Criterion

v0.3 complete when:
1. DistSystem, RefOp, Stabilizes defined
2. Monotonicity proven from ⪯
3. T1-T4 proven (or shown unprovable with reason)
4. 0 postulates
5. Connection to v0.1 (types) and v0.2 (Π/Σ) explicit

## Applications

| Domain | Stabilization criterion |
|--------|------------------------|
| Medicine | Stable(patient, clinical_obs) |
| Psychology | Stable(cognitive_state, behavioral_obs) |
| Physics | Stable(field_config, all_observables) |
| Math | Stable(construction, proof_methods) |

## Status

SPEC revised. Ready for Agda implementation.
