# Lean formalization related to Erdős Problem #117

This repository contains a Lean 4 / Mathlib formalization of the main result of

*Sharp Asymptotics for Abelian Covers of Groups with Bounded Noncommutativity*.

The principal formal theorem is:

    AbelianCovers.main_theorem

Conditional on six explicitly stated classical external results, the development proves

    log₂ h(n) = n/2 + O(√n (log(n+2))³),

and consequently

    h(n)^(1/n) → √2.

The six external inputs are represented explicitly as hypotheses:

- NeumannCentreQuotientFinite
- SchurDerivedFinite
- HallStemTheorem
- PyberCentreIndex
- NeumannVaughanLeeBound
- ExtraspecialExists

The development contains no `sorry` or `admit`.

The final theorem can be audited using:

    #print axioms AbelianCovers.main_theorem
    #print axioms AbelianCovers.hFun_root_tendsto

## Build

The development uses Lean 4 and Mathlib.

    lake build
