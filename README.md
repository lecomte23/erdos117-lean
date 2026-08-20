# Lean formalization of sharp exponential asymptotics for Erdős Problem #117

This repository contains a Lean 4 / Mathlib formalization of sharp exponential asymptotics for the function (h(n)) appearing in Erdős Problem #117.

The principal formal result is the theorem

```lean
AbelianCovers.main_theorem
```

which proves, conditional on six explicitly stated classical external results, that there exists an absolute constant (C>0) such that for every (n\in\mathbb N),

[
\left|\log_2 h(n)-\frac n2\right|
\le
C\sqrt n,(\log(n+2))^3.
]

In particular,

[
\log_2 h(n)
===========

\frac n2
+
O!\left(\sqrt n(\log(n+2))^3\right),
]

and therefore

[
h(n)^{1/n}\longrightarrow \sqrt 2.
]

The corresponding Lean theorem for the root asymptotic is

```lean
AbelianCovers.hFun_root_tendsto
```

## 1. Mathematical definitions

The formalization works with the following quantities.

For a group (G), `omegaG G` is the supremum of the cardinalities of finite pairwise noncommuting subsets of (G):

```lean
noncomputable def omegaG (G : Type*) [Group G] : ℕ∞ := ...
```

A finite family of subgroups is an abelian cover if every subgroup in the family is abelian and their union is the whole group. The quantity `aG G` is the least number of abelian subgroups required to cover (G).

The extremal function is formalized as

```lean
noncomputable def hFun (n : ℕ) : ℕ∞ :=
  sSup {a : ℕ∞ | ∃ (G : Type) (inst : Group G),
    @omegaG G inst ≤ (n : ℕ∞) ∧ @aG G inst = a}
```

Thus `hFun n` is the supremum of the abelian covering numbers of groups satisfying (\omega(G)\le n).

Finally,

```lean
noncomputable def log2h (n : ℕ) : ℝ :=
  Real.logb 2 ((hFun n).toNat)
```

is the quantity estimated in the main theorem.

## 2. Main theorem

The precise Lean statement is:

```lean
theorem main_theorem
    (hNeu : NeumannCentreQuotientFinite)
    (hSchur : SchurDerivedFinite)
    (hHall : HallStemTheorem)
    (hPyber : PyberCentreIndex)
    (hNVL : NeumannVaughanLeeBound)
    (hE : ExtraspecialExists) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      |log2h n - (n : ℝ) / 2|
        ≤ C * Real.sqrt n * (Real.log (n + 2)) ^ 3
```

The root-asymptotic consequence is:

```lean
theorem hFun_root_tendsto
    (hNeu : NeumannCentreQuotientFinite)
    (hSchur : SchurDerivedFinite)
    (hHall : HallStemTheorem)
    (hPyber : PyberCentreIndex)
    (hNVL : NeumannVaughanLeeBound)
    (hE : ExtraspecialExists) :
    Filter.Tendsto
      (fun n : ℕ => (((hFun n).toNat : ℝ)) ^ ((1 : ℝ) / n))
      Filter.atTop
      (nhds (Real.sqrt 2))
```

This identifies the sharp exponential scale of (h(n)).

## 3. External mathematical inputs

The main theorem is conditional on six classical results. They are not inserted as hidden Lean axioms. Each is defined as a proposition and passed explicitly as a hypothesis to every theorem that requires it.

### 3.1 B. H. Neumann: finiteness of the central quotient

```lean
def NeumannCentreQuotientFinite : Prop :=
  ∀ (G : Type) [Group G] (n : ℕ),
    omegaG G ≤ (n : ℕ∞) →
    Finite (G ⧸ Subgroup.center G)
```

This expresses that bounded size of pairwise noncommuting subsets forces (G/Z(G)) to be finite.

### 3.2 Schur's theorem

```lean
def SchurDerivedFinite : Prop :=
  ∀ (G : Type) [Group G],
    Finite (G ⧸ Subgroup.center G) →
    Finite (commutator G)
```

This is the classical implication that finite (G/Z(G)) implies finite derived subgroup (G').

### 3.3 P. Hall's stem-group theorem

The formal statement asserts that every group is isoclinic to a group (H) satisfying

[
Z(H)\le H'.
]

### 3.4 Pyber's centre-index bound

```lean
def PyberCentreIndex : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧
    ∀ (G : Type) [Group G] [Finite G] (N : ℕ),
      omegaG G ≤ (N : ℕ∞) →
      ((Subgroup.center G).index : ℝ) ≤ C ^ N
```

This supplies an exponential bound on the index of the centre in terms of the noncommuting-set parameter.

### 3.5 Neumann–Vaughan-Lee BFC bound

In the form used here, an (r)-BFC group satisfies

[
|G'|
\le
r^{(3+5\log_2 r)/2}.
]

### 3.6 Existence of extraspecial (2)-groups

```lean
def ExtraspecialExists : Prop :=
  ∀ m : ℕ,
    ∃ (E : Type) (inst : Group E),
      Finite E ∧ Nonempty (@ExtraspecialData m E inst)
```

This supplies the explicit lower-bound family used in the proof.

The source file also defines a proposition `NeumannCoveringLemma`, but it is **not** one of the six hypotheses of `AbelianCovers.main_theorem`.

For bibliographic details and the mathematical role of these inputs, see the accompanying manuscript or the references associated with the project.

## 4. Formalization status

The Lean source is designed so that the distinction between formalized arguments and external mathematical inputs is explicit.

In particular:

* the source contains no `sorry`;
* the source contains no `admit`;
* the source does not declare the six external results with the Lean `axiom` command;
* each external result is represented by a named proposition and supplied as an explicit theorem parameter;
* the main asymptotic derivation from those six inputs is formalized in Lean.

Two explicit audit commands are included at the end of the source file:

```lean
#print axioms AbelianCovers.main_theorem
#print axioms AbelianCovers.hFun_root_tendsto
```

These allow a reviewer to inspect the logical axioms used by Lean after compilation.

The presence of standard logical axioms inherited from Lean/Mathlib, such as classical choice or quotient-related principles, should be distinguished from `sorryAx` or from user-declared mathematical axioms.

## 5. Repository contents

The principal source file is:

```text
Erdos117.lean
```

For a fully reproducible build, the repository should also contain the project files pinning the Lean and Mathlib environment, typically:

```text
lean-toolchain
lakefile.toml
lake-manifest.json
```

These files should correspond to the exact environment in which `Erdos117.lean` was checked.

## 6. Building and checking

Assuming the repository contains the corresponding Lake project configuration and pinned Mathlib environment:

```bash
lake update
lake build
```

A successful build should be followed by inspection of the output of:

```lean
#print axioms AbelianCovers.main_theorem
#print axioms AbelianCovers.hFun_root_tendsto
```

A reviewer should in particular verify that no `sorryAx` appears.

## 7. Scope of the claim

This repository makes a precise formal claim:

> Conditional on the six explicitly stated classical external results, Lean verifies the derivation of the sharp exponential asymptotic
>
> [
> \log_2 h(n)
> ===========
>
> \frac n2
> +
> O!\left(\sqrt n(\log(n+2))^3\right),
> ]
>
> and hence
>
> [
> h(n)^{1/n}\to\sqrt2.
> ]

The repository deliberately separates this machine-checkable statement from the distinct editorial or historical question of whether the result should be classified by the maintainers of the Erdős Problems project as a complete resolution of Problem #117.

## 8. Reproducibility and review

For archival or review purposes, references to this formalization should preferably use a GitHub URL pinned to a specific commit SHA rather than a moving `main`-branch URL.

For example:

```text
https://github.com/<username>/<repository>/blob/<commit-sha>/Erdos117.lean
```

This ensures that the cited formal artifact cannot change after it has been reviewed.

## 9. AI assistance disclosure

AI tools were used during the development, formalization, checking, refactoring, and documentation of the Lean code.
The mathematical claims are presented in a form intended to be independently auditable:

* the Lean source is public;
* the external mathematical inputs are explicit;
* the central theorem has a precise formal statement;
* the source contains explicit `#print axioms` checks;
* the complete development is intended to be independently reproducible in the pinned Lean/Mathlib environment.

Machine verification does not replace independent mathematical review of the external inputs, their bibliographic provenance, or the interpretation of the result relative to the original formulation of Erdős Problem #117.

## 10. Citation

If this repository is cited, please cite both the exact commit of the Lean formalization and the corresponding mathematical manuscript when available.

A permanent commit-pinned link is preferred over a link to the moving `main` branch.

---

**Primary formal theorem:** `AbelianCovers.main_theorem`
**Asymptotic consequence:** `AbelianCovers.hFun_root_tendsto`
**Proof assistant:** Lean 4
**Library:** Mathlib
