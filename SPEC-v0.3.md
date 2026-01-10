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

**T1 (Direct):** ¬Closure → ∃x. ¬StabilizesRobust x

### Key Structures

```agda
-- witnessComp: composition distinguishes what individuals can't
witnessComp : ∀ d d1 d2 → ∃x,y. (d1,d2 can't distinguish) × (comp CAN)

-- Potential split: pair that comp WOULD distinguish
T1-potential-split : ∀ d₀ n d1 d2 → 
  let (x, y, eq1, eq2, neq) = witnessComp ...
  in eq1 × eq2 × neq  -- d1,d2 agree, comp disagrees

-- Robust stabilization: stable under ALL refinement operators
StabilizesRobust x d₀ = ∀ alt. ∃k. x stable at k under alt
```

### Proof Structure

1. witnessComp gives (x, y) distinguishable by comp but not by d1, d2
2. T1-potential-split: this is a "potential split" 
3. Non-closure: some comp never added to trajectory
4. Therefore: (x, y) remains "falsely equivalent" on trajectory
5. Robust stability requires: stable under ALL extensions
6. Non-closure → false equivalences → robust stability impossible

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

## T3: Collapse-3 (FULLY PROVEN)

### Statement

**T3 (Constancy Theorem):** Universal d₀ + StableK d₀ K → Constant K

"If refinement starts from 'no distinctions' and K respects all trajectory steps, K must be constant."

### Two Proof Forms

**Form 1: Universal Base**
```agda
Universal d₀ = ∀ x y → x ~[d₀] y  -- all equivalent at start

T3-constancy : Universal d₀ → StableK d₀ K → Constant K
T3-constancy univ stable x y = stable zero (univ x y)
```

**Form 2: Connectivity**
```agda
data Connected d₀ : U → U → Set where
  conn-refl : Connected d₀ x x
  conn-step : x ~[traj n] y → Connected d₀ y z → Connected d₀ x z

FullyConnected d₀ = ∀ x y → Connected d₀ x y

T3-connected : FullyConnected d₀ → StableK d₀ K → Constant K
T3-connected conn K stable x y = stable-respects-path (conn x y)
```

### The Role of Drift

Drift ensures Universal persists:
- Classes always split → never stabilize into nontrivial partitions
- So if you start universal, you stay "effectively universal" for knowledge purposes

### File

`src/Distinction/ForcingT3.agda` — compiles, 0 postulates, **FULLY PROVEN**

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
