import Mathlib

/-!
# Sharp asymptotics for abelian covers of groups with bounded noncommutativity

This file is a single-file formalisation of the manuscript

  *Sharp Asymptotics for Abelian Covers of Groups with Bounded Noncommutativity*,

which determines the sharp exponential growth rate of

  `h(n) = sup { a(G) : ω(G) ≤ n }`,

where `ω(G)` is the largest size of a pairwise noncommuting subset of `G` and `a(G)` is the
least size of a cover of `G` by abelian subgroups.  The main result is

  `log₂ h(n) = n/2 + O(√n (log (n+2))³)`.

## Conventions

* `ω(G)` and `a(G)` are formalised as elements of `ℕ∞` (`omegaG`, `aG`), so that the degenerate
  cases (no finite noncommuting set, no finite abelian cover) are recorded as `⊤` rather than by
  an arbitrary junk value.
* `h(n)` (`hFun`) is a supremum over groups carried by types in `Type 0`.  Since both parameters
  are isomorphism invariants and, by the finite reduction of Section 2, are attained on finite
  groups, this is no loss of generality.
* Results quoted from the literature and treated as black boxes in the manuscript are formalised
  as `Prop`-valued definitions in Section 1 and are passed as *hypotheses* to the statements that
  use them, exactly as the manuscript uses them as external input.

## References

The bracketed numbers refer to the bibliography of the manuscript, e.g. [23] = Pyber,
[24] = Neumann–Vaughan-Lee, [20] = B. H. Neumann, [21] = P. Hall.
-/

open scoped BigOperators
open scoped Real
open scoped Classical
open scoped Pointwise
open scoped commutatorElement

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace AbelianCovers

universe u

/-! ## 0. The two parameters -/

/-- A set of group elements is *noncommuting* if any two distinct members fail to commute.
These are the cliques of the noncommuting graph `Γ_G`. -/
def IsNoncommSet {G : Type*} [Group G] (S : Set G) : Prop :=
  ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ¬ Commute x y

/-- `ω(G)`: the supremum of the sizes of pairwise noncommuting subsets of `G`. -/
noncomputable def omegaG (G : Type*) [Group G] : ℕ∞ :=
  ⨆ S : {S : Finset G // IsNoncommSet (S : Set G)}, ((S : Finset G).card : ℕ∞)

/-- A finite family of subgroups is an *abelian cover* if each member is abelian and the union of
the members is the whole group. -/
def IsAbelianCover {G : Type*} [Group G] (C : Finset (Subgroup G)) : Prop :=
  (∀ A ∈ C, ∀ x ∈ A, ∀ y ∈ A, Commute x y) ∧ ∀ g : G, ∃ A ∈ C, g ∈ A

/-- `a(G)`: the least number of abelian subgroups needed to cover `G`. -/
noncomputable def aG (G : Type*) [Group G] : ℕ∞ :=
  ⨅ C : {C : Finset (Subgroup G) // IsAbelianCover C}, ((C : Finset (Subgroup G)).card : ℕ∞)

/-- The least number of abelian subgroups of `G` whose union contains a given subset `X ⊆ G`.
This is the quantity `a(X)` of Lemma 8.1. -/
noncomputable def aSet {G : Type*} [Group G] (X : Set G) : ℕ∞ :=
  ⨅ C : {C : Finset (Subgroup G) //
      (∀ A ∈ C, ∀ x ∈ A, ∀ y ∈ A, Commute x y) ∧ ∀ g ∈ X, ∃ A ∈ C, g ∈ A},
    ((C : Finset (Subgroup G)).card : ℕ∞)

/-- `h(n) = sup { a(G) : ω(G) ≤ n }`. -/
noncomputable def hFun (n : ℕ) : ℕ∞ :=
  sSup {a : ℕ∞ | ∃ (G : Type) (inst : Group G), @omegaG G inst ≤ (n : ℕ∞) ∧ @aG G inst = a}

/-- `log₂ h(n)`, the quantity estimated by the main theorem. -/
noncomputable def log2h (n : ℕ) : ℝ := Real.logb 2 ((hFun n).toNat)

theorem omegaG_le_iff (G : Type*) [Group G] (n : ℕ) :
    omegaG G ≤ (n : ℕ∞) ↔ ∀ S : Finset G, IsNoncommSet (S : Set G) → S.card ≤ n := by
  constructor
  · intro h S hS
    have : ((S.card : ℕ∞)) ≤ (n : ℕ∞) := le_trans (le_iSup (fun T : {T : Finset G //
      IsNoncommSet (T : Set G)} => (((T : Finset G).card : ℕ∞))) ⟨S, hS⟩) h
    exact_mod_cast this
  · intro h
    refine iSup_le ?_
    rintro ⟨S, hS⟩
    exact_mod_cast h S hS

theorem card_le_omegaG {G : Type*} [Group G] (S : Finset G) (hS : IsNoncommSet (S : Set G)) :
    (S.card : ℕ∞) ≤ omegaG G :=
  le_iSup (fun T : {T : Finset G // IsNoncommSet (T : Set G)} => (((T : Finset G).card : ℕ∞)))
    ⟨S, hS⟩

theorem aG_le_of_cover {G : Type*} [Group G] (C : Finset (Subgroup G)) (hC : IsAbelianCover C) :
    aG G ≤ (C.card : ℕ∞) :=
  iInf_le (fun D : {D : Finset (Subgroup G) // IsAbelianCover D} =>
    (((D : Finset (Subgroup G)).card : ℕ∞))) ⟨C, hC⟩

/-! ## 1. External results used as black boxes

Each of the following is a classical theorem quoted in the manuscript.  They are formalised as
propositions and appear as explicit hypotheses of the results that use them. -/

/-- Two groups are *isoclinic* when there are isomorphisms of their central quotients and of
their derived subgroups which are compatible with the commutator maps. -/
structure Isoclinic (G H : Type) [Group G] [Group H] : Type where
  /-- The isomorphism of central quotients. -/
  toQuot : (G ⧸ Subgroup.center G) ≃* (H ⧸ Subgroup.center H)
  /-- The isomorphism of derived subgroups. -/
  toDer : (commutator G) ≃* (commutator H)
  /-- Compatibility of the two isomorphisms with commutators. -/
  compat : ∀ (x y : G) (x' y' : H),
      toQuot (QuotientGroup.mk x) = QuotientGroup.mk x' →
      toQuot (QuotientGroup.mk y) = QuotientGroup.mk y' →
      (toDer ⟨⁅x, y⁆, Subgroup.commutator_mem_commutator
        (Subgroup.mem_top x) (Subgroup.mem_top y)⟩ : H) = ⁅x', y'⁆

/-- **B. H. Neumann** [20]: if the pairwise noncommuting subsets of `G` have bounded size, then
`G/Z(G)` is finite. -/
def NeumannCentreQuotientFinite : Prop :=
  ∀ (G : Type) [Group G] (n : ℕ), omegaG G ≤ (n : ℕ∞) → Finite (G ⧸ Subgroup.center G)

/-- **Schur's theorem**: if `G/Z(G)` is finite then `G'` is finite. -/
def SchurDerivedFinite : Prop :=
  ∀ (G : Type) [Group G], Finite (G ⧸ Subgroup.center G) → Finite (commutator G)

/-- **P. Hall's stem group theorem** [21]: every group is isoclinic to a group `H` with
`Z(H) ≤ H'`. -/
def HallStemTheorem : Prop :=
  ∀ (G : Type) [Group G], ∃ (H : Type) (inst : Group H),
    Nonempty (@Isoclinic G H _ inst) ∧ @Subgroup.center H inst ≤ @commutator H inst

/-- **Pyber's centre-index theorem** [23]: `[G : Z(G)] ≤ C^{ω(G)}` for an absolute constant `C`. -/
def PyberCentreIndex : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (G : Type) [Group G] [Finite G] (N : ℕ), omegaG G ≤ (N : ℕ∞) →
    ((Subgroup.center G).index : ℝ) ≤ C ^ N

/-- **Neumann–Vaughan-Lee** [24]: in an `r`-BFC group, `|G'| ≤ r^{(3 + 5 log₂ r)/2}`. -/
def NeumannVaughanLeeBound : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (r : ℕ), 1 ≤ r →
    (∀ g : G, (Subgroup.centralizer ({g} : Set G)).index ≤ r) →
    (Nat.card (commutator G) : ℝ) ≤ (r : ℝ) ^ ((3 + 5 * Real.logb 2 r) / 2)

/-- **B. H. Neumann's covering lemma** [20]: if a group is covered by `k` subgroups,
one of those subgroups has finite index at most `k`. -/
def NeumannCoveringLemma : Prop :=
  ∀ (G : Type) [Group G] (k : ℕ) (C : Finset (Subgroup G)), C.card = k →
    (∀ g : G, ∃ A ∈ C, g ∈ A) → ∃ A ∈ C, 0 < A.index ∧ A.index ≤ k

/-! ## 2. Statement and finite reduction -/

namespace Isoclinic

variable {G H : Type} [Group G] [Group H]

/-- Isoclinic groups have the same commutation relations: if `x, y` and `x', y'` correspond
under the isomorphism of central quotients, then `x` commutes with `y` if and only if `x'`
commutes with `y'`. -/
theorem commute_iff (I : Isoclinic G H) {x y : G} {x' y' : H}
    (hx : I.toQuot (QuotientGroup.mk x) = QuotientGroup.mk x')
    (hy : I.toQuot (QuotientGroup.mk y) = QuotientGroup.mk y') :
    Commute x y ↔ Commute x' y' := by
  have h := I.compat x y x' y' hx hy
  rw [← commutatorElement_eq_one_iff_commute, ← commutatorElement_eq_one_iff_commute, ← h,
    OneMemClass.coe_eq_one, EmbeddingLike.map_eq_one_iff]
  exact ⟨fun hc => Subtype.ext hc, fun hc => congrArg Subtype.val hc⟩

/-- Isoclinism is a symmetric relation. -/
def symm (I : Isoclinic G H) : Isoclinic H G where
  toQuot := I.toQuot.symm
  toDer := I.toDer.symm
  compat := by
    intro x' y' x y hx hy
    have hx' : I.toQuot (QuotientGroup.mk x) = QuotientGroup.mk x' := by rw [← hx]; simp
    have hy' : I.toQuot (QuotientGroup.mk y) = QuotientGroup.mk y' := by rw [← hy]; simp
    have h := I.compat x y x' y' hx' hy'
    have he : (⟨⁅x', y'⁆, Subgroup.commutator_mem_commutator
        (Subgroup.mem_top x') (Subgroup.mem_top y')⟩ : commutator H)
        = I.toDer ⟨⁅x, y⁆, Subgroup.commutator_mem_commutator
        (Subgroup.mem_top x) (Subgroup.mem_top y)⟩ := Subtype.ext h.symm
    rw [he, MulEquiv.symm_apply_apply]

end Isoclinic

/-- One inequality of Lemma 2.1 for `ω`: a noncommuting set of `G` is transported to a
noncommuting set of `H` of the same size. -/
theorem omegaG_le_of_isoclinic {G H : Type} [Group G] [Group H] (I : Isoclinic G H) :
    omegaG G ≤ omegaG H := by
  refine iSup_le ?_
  rintro ⟨S, hS⟩
  set f : G → H := fun x => Quotient.out (I.toQuot (QuotientGroup.mk x)) with hf_def
  have hf : ∀ x : G, QuotientGroup.mk (f x) = I.toQuot (QuotientGroup.mk x) := fun x =>
    QuotientGroup.out_eq' _
  have hinj : Set.InjOn f (S : Set G) := by
    intro x hx y hy hxy
    by_contra hne
    refine hS hx hy hne ?_
    refine (I.commute_iff (x' := f x) (y' := f y) (hf x).symm (hf y).symm).mpr ?_
    rw [hxy]
  have hnc : IsNoncommSet ((S.image f : Finset H) : Set H) := by
    intro u hu v hv huv
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hu hv
    obtain ⟨x, hx, rfl⟩ := hu
    obtain ⟨y, hy, rfl⟩ := hv
    have hne : x ≠ y := fun h => huv (by rw [h])
    exact fun hc => hS hx hy hne
      ((I.commute_iff (x' := f x) (y' := f y) (hf x).symm (hf y).symm).mpr hc)
  have hcard := card_le_omegaG (S.image f) hnc
  rwa [Finset.card_image_of_injOn hinj] at hcard

/-- One inequality of Lemma 2.1 for `a`: an abelian cover of `G` is transported to an abelian
cover of `H` with at most as many members. -/
theorem aG_le_of_isoclinic {G H : Type} [Group G] [Group H] (I : Isoclinic G H) :
    aG H ≤ aG G := by
  refine le_iInf ?_
  rintro ⟨C, hC⟩
  set psi : Subgroup G → Subgroup H := fun A =>
    Subgroup.comap (QuotientGroup.mk' (Subgroup.center H))
      (Subgroup.map I.toQuot.toMonoidHom
        (Subgroup.map (QuotientGroup.mk' (Subgroup.center G)) A)) with hpsi
  have hmem : ∀ (A : Subgroup G) (x' : H), x' ∈ psi A ↔
      ∃ a ∈ A, I.toQuot (QuotientGroup.mk a) = QuotientGroup.mk x' := by
    intro A x'
    simp [hpsi, Subgroup.mem_comap, Subgroup.mem_map, QuotientGroup.mk'_apply]
  have hcov : IsAbelianCover (C.image psi) := by
    constructor
    · intro B hB x' hx' y' hy'
      simp only [Finset.mem_image] at hB
      obtain ⟨A, hA, rfl⟩ := hB
      obtain ⟨a, ha, hax⟩ := (hmem A x').mp hx'
      obtain ⟨b, hb, hby⟩ := (hmem A y').mp hy'
      exact (I.commute_iff hax hby).mp (hC.1 A hA a ha b hb)
    · intro g'
      set q : G ⧸ Subgroup.center G := I.toQuot.symm (QuotientGroup.mk g') with hq
      have hgq : QuotientGroup.mk (Quotient.out q) = q := QuotientGroup.out_eq' _
      have hgg : I.toQuot (QuotientGroup.mk (Quotient.out q)) = QuotientGroup.mk g' := by
        rw [hgq, hq, MulEquiv.apply_symm_apply]
      obtain ⟨A, hA, hgA⟩ := hC.2 (Quotient.out q)
      exact ⟨psi A, Finset.mem_image_of_mem _ hA, (hmem A g').mpr ⟨_, hgA, hgg⟩⟩
  calc aG H ≤ (((C.image psi).card : ℕ) : ℕ∞) := aG_le_of_cover _ hcov
    _ ≤ ((C.card : ℕ) : ℕ∞) := by exact_mod_cast Finset.card_image_le

/-- Half of Lemma 2.1: `ω` is an isoclinism invariant. -/
theorem omegaG_eq_of_isoclinic {G H : Type} [Group G] [Group H] (I : Isoclinic G H) :
    omegaG G = omegaG H :=
  le_antisymm (omegaG_le_of_isoclinic I) (omegaG_le_of_isoclinic I.symm)

/-- Half of Lemma 2.1: `a` is an isoclinism invariant. -/
theorem aG_eq_of_isoclinic {G H : Type} [Group G] [Group H] (I : Isoclinic G H) :
    aG G = aG H :=
  le_antisymm (aG_le_of_isoclinic I.symm) (aG_le_of_isoclinic I)

/-- **Lemma 2.1** (Finite reduction by isoclinism).  A group with a bounded noncommuting set is
isoclinic to a finite group with the same two parameters. -/
theorem finite_reduction (hNeu : NeumannCentreQuotientFinite) (hSchur : SchurDerivedFinite)
    (hHall : HallStemTheorem) (G : Type) [Group G] (n : ℕ) (hG : omegaG G ≤ (n : ℕ∞)) :
    ∃ (H : Type) (inst : Group H), Finite H ∧ @omegaG H inst = omegaG G ∧ @aG H inst = aG G := by
  obtain ⟨H, instH, ⟨I⟩, hZ⟩ := hHall G
  have hom : @omegaG H instH = omegaG G := (omegaG_eq_of_isoclinic I).symm
  have ha : @aG H instH = aG G := (aG_eq_of_isoclinic I).symm
  have hq : Finite (H ⧸ @Subgroup.center H instH) := hNeu H n (by rw [hom]; exact hG)
  have hd : Finite (@commutator H instH) := hSchur H hq
  have hz : Finite (@Subgroup.center H instH) :=
    Finite.of_injective (Subgroup.inclusion hZ) (Subgroup.inclusion_injective hZ)
  exact ⟨H, instH, Finite.of_subgroup_quotient (@Subgroup.center H instH), hom, ha⟩

/-- **Lemma 2.1**, consequence: `h(n)` may be computed over finite groups only. -/
theorem hFun_eq_sup_finite (hNeu : NeumannCentreQuotientFinite) (hSchur : SchurDerivedFinite)
    (hHall : HallStemTheorem) (n : ℕ) :
    hFun n = sSup {a : ℕ∞ | ∃ (H : Type) (inst : Group H), Finite H ∧
      @omegaG H inst ≤ (n : ℕ∞) ∧ @aG H inst = a} := by
  apply le_antisymm
  · apply sSup_le
    rintro a ⟨G, inst, hom, rfl⟩
    obtain ⟨H, instH, hfin, hom', ha'⟩ := finite_reduction hNeu hSchur hHall G n hom
    exact le_sSup ⟨H, instH, hfin, by rw [hom']; exact hom, ha'⟩
  · apply sSup_le
    rintro a ⟨H, instH, _, hom, ha⟩
    exact le_sSup ⟨H, instH, hom, ha⟩

/-! ## 3. Global compression estimates -/

/-- Greedy domination: inside any finite subset `T` of a group there is a pairwise noncommuting
subset `S ⊆ T` such that every element of `T` commutes with some element of `S`. -/
theorem exists_noncomm_dominating {G : Type} [Group G] (T : Finset G) :
    ∃ S : Finset G, S ⊆ T ∧ IsNoncommSet (S : Set G) ∧ ∀ t ∈ T, ∃ s ∈ S, Commute t s := by
  classical
  obtain ⟨S, hSmem, hSmax⟩ := Finset.exists_max_image
    (T.powerset.filter (fun U : Finset G => IsNoncommSet (U : Set G))) Finset.card
    ⟨∅, by simp [IsNoncommSet]⟩
  simp only [Finset.mem_filter, Finset.mem_powerset] at hSmem
  refine ⟨S, hSmem.1, hSmem.2, ?_⟩
  intro t ht
  by_cases htS : t ∈ S
  · exact ⟨t, htS, Commute.refl t⟩
  · have hins : ¬ IsNoncommSet ((insert t S : Finset G) : Set G) := by
      intro hcon
      have hmem : (insert t S) ∈
          (T.powerset.filter (fun U : Finset G => IsNoncommSet (U : Set G))) := by
        simp only [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.insert_subset ht hSmem.1, hcon⟩
      have := hSmax _ hmem
      rw [Finset.card_insert_of_notMem htS] at this
      omega
    unfold IsNoncommSet at hins
    push Not at hins
    obtain ⟨x, hx, y, hy, hxy, hcomm⟩ := hins
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · exact absurd rfl hxy
      · exact ⟨y, hy, hcomm⟩
    · rcases hy with rfl | hy
      · exact ⟨x, hx, hcomm.symm⟩
      · exact absurd hcomm (hSmem.2 hx hy hxy)

/-- The greedy bound `ω(G) ≥ |T| / max_{x ∈ T} |C_G(x)|` of Lemma 3.1. -/
theorem card_le_omega_mul_centralizer {G : Type} [Group G] [Fintype G] (N m : ℕ)
    (hN : omegaG G ≤ (N : ℕ∞)) (T : Finset G)
    (hm : ∀ x ∈ T, Nat.card (Subgroup.centralizer ({x} : Set G)) ≤ m) :
    T.card ≤ N * m := by
  classical
  obtain ⟨S, hST, hS, hdom⟩ := exists_noncomm_dominating T
  have hSN : S.card ≤ N := (omegaG_le_iff G N).mp hN S hS
  have hcard : ∀ s : G, ((Subgroup.centralizer ({s} : Set G) : Set G).toFinset).card
      = Nat.card (Subgroup.centralizer ({s} : Set G)) := by
    intro s
    rw [Set.toFinset_card, Nat.card_eq_fintype_card]
    rfl
  have hsub : T ⊆ S.biUnion (fun s => (Subgroup.centralizer ({s} : Set G) : Set G).toFinset) := by
    intro t ht
    obtain ⟨s, hs, hcomm⟩ := hdom t ht
    refine Finset.mem_biUnion.mpr ⟨s, hs, ?_⟩
    simp only [Set.mem_toFinset, SetLike.mem_coe, Subgroup.mem_centralizer_iff,
      Set.mem_singleton_iff]
    rintro g rfl
    exact hcomm.symm
  calc T.card
      ≤ (S.biUnion (fun s => (Subgroup.centralizer ({s} : Set G) : Set G).toFinset)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ s ∈ S, ((Subgroup.centralizer ({s} : Set G) : Set G).toFinset).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _s ∈ S, m := Finset.sum_le_sum (fun s hs => by
        rw [hcard s]; exact hm s (hST hs))
    _ = S.card * m := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ N * m := Nat.mul_le_mul_right m hSN

theorem centralizer_inv {G : Type} [Group G] (x : G) :
    Subgroup.centralizer ({x⁻¹} : Set G) = Subgroup.centralizer ({x} : Set G) := by
  ext z
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  exact ⟨fun h => (Commute.inv_left_iff (a := x) (b := z)).mp h,
    fun h => (Commute.inv_left_iff (a := x) (b := z)).mpr h⟩

theorem centralizer_mul_le {G : Type} [Group G] (a b : G) :
    Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) ≤
      Subgroup.centralizer ({a * b} : Set G) := by
  intro z hz
  rw [Subgroup.mem_inf] at hz
  obtain ⟨hza, hzb⟩ := hz
  rw [Subgroup.mem_centralizer_iff] at hza hzb ⊢
  rintro g hg
  simp only [Set.mem_singleton_iff] at hg
  subst hg
  have h1 := hza a rfl
  have h2 := hzb b rfl
  calc a * b * z = a * (b * z) := by rw [mul_assoc]
    _ = a * (z * b) := by rw [h2]
    _ = (a * z) * b := by rw [mul_assoc]
    _ = (z * a) * b := by rw [h1]
    _ = z * (a * b) := by rw [mul_assoc]

/-- **Lemma 3.1** (Polynomial BFC bound): every conjugacy class of a finite group `G` has size at
most `(2 ω(G) + 1)²`. -/
theorem conjClass_index_le {G : Type} [Group G] [Finite G] (N : ℕ) (hN : omegaG G ≤ (N : ℕ∞))
    (g : G) : (Subgroup.centralizer ({g} : Set G)).index ≤ (2 * N + 1) ^ 2 := by
  classical
  cases nonempty_fintype G
  have hcardG : 0 < Nat.card G := Nat.card_pos
  have hindex_pos : ∀ H : Subgroup G, 0 < H.index := by
    intro H
    have := H.card_mul_index
    rcases Nat.eq_zero_or_pos H.index with h | h
    · rw [h, mul_zero] at this; omega
    · exact h
  set m := 2 * N + 1 with hm
  set Y : Finset G :=
    Finset.univ.filter (fun x => (Subgroup.centralizer ({x} : Set G)).index ≤ m) with hY
  set Z : Finset G :=
    Finset.univ.filter (fun x => ¬ (Subgroup.centralizer ({x} : Set G)).index ≤ m) with hZ
  set d : ℕ := Nat.card G / (2 * N + 2) with hd
  have hZcard : Z.card ≤ N * d := by
    refine card_le_omega_mul_centralizer N d hN Z ?_
    intro x hx
    simp only [hZ, Finset.mem_filter, not_le] at hx
    have hxi : 2 * N + 2 ≤ (Subgroup.centralizer ({x} : Set G)).index := by omega
    have hmi := (Subgroup.centralizer ({x} : Set G)).card_mul_index
    rw [hd, Nat.le_div_iff_mul_le (by omega)]
    calc Nat.card (Subgroup.centralizer ({x} : Set G)) * (2 * N + 2)
        ≤ Nat.card (Subgroup.centralizer ({x} : Set G))
            * (Subgroup.centralizer ({x} : Set G)).index := Nat.mul_le_mul_left _ hxi
      _ = Nat.card G := hmi
  have hZlt : 2 * Z.card < Nat.card G := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · rw [h0, mul_zero] at hZcard; omega
    · have hdle : d * (2 * N + 2) ≤ Nat.card G := Nat.div_mul_le_self _ _
      have : 2 * (N * d) + 2 * d ≤ Nat.card G := by
        calc 2 * (N * d) + 2 * d = d * (2 * N + 2) := by ring
          _ ≤ Nat.card G := hdle
      omega
  have hYZ : Y.card + Z.card = Nat.card G := by
    rw [hY, hZ, Finset.card_filter_add_card_filter_not, Nat.card_eq_fintype_card,
      Finset.card_univ]
  have hYbig : Nat.card G < 2 * Y.card := by omega
  have key : ∀ z : G, ∃ y₁ ∈ Y, ∃ y₂ ∈ Y, z = y₁ * y₂⁻¹ := by
    intro z
    by_contra hcon
    push Not at hcon
    have hdisj : Disjoint Y (Y.image (fun y => z * y)) := by
      rw [Finset.disjoint_left]
      intro w hw hw2
      simp only [Finset.mem_image] at hw2
      obtain ⟨y₂, hy₂, rfl⟩ := hw2
      exact (hcon (z * y₂) hw y₂ hy₂) (by group)
    have himg : (Y.image (fun y => z * y)).card = Y.card :=
      Finset.card_image_of_injective _ (fun a b hab => by simpa using hab)
    have hu := Finset.card_union_of_disjoint hdisj
    have hle : (Y ∪ Y.image (fun y => z * y)).card ≤ Nat.card G := by
      rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ _)
    omega
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := key g
  simp only [hY, Finset.mem_filter] at hy₁ hy₂
  have h1 : (Subgroup.centralizer ({y₁} : Set G)).index ≤ m := hy₁.2
  have h2 : (Subgroup.centralizer ({y₂⁻¹} : Set G)).index ≤ m := by
    rw [centralizer_inv]; exact hy₂.2
  calc (Subgroup.centralizer ({y₁ * y₂⁻¹} : Set G)).index
      ≤ (Subgroup.centralizer ({y₁} : Set G) ⊓ Subgroup.centralizer ({y₂⁻¹} : Set G)).index :=
        Nat.le_of_dvd (hindex_pos _) (Subgroup.index_dvd_of_le (centralizer_mul_le y₁ y₂⁻¹))
    _ ≤ (Subgroup.centralizer ({y₁} : Set G)).index
          * (Subgroup.centralizer ({y₂⁻¹} : Set G)).index := Subgroup.index_inf_le
    _ ≤ m * m := Nat.mul_le_mul h1 h2
    _ = (2 * N + 1) ^ 2 := by rw [hm]; ring

/-- **Corollary 3.2** (Small derived subgroup): `log₂ |G'| ≤ C (log₂ (N+2))²`. -/
theorem log2_card_commutator_le (hNVL : NeumannVaughanLeeBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (G : Type) [Group G] [Finite G] (N : ℕ), omegaG G ≤ (N : ℕ∞) →
      Real.logb 2 (Nat.card (commutator G)) ≤ C * (Real.logb 2 (N + 2)) ^ 2 := by
  refine ⟨46, by norm_num, ?_⟩
  intro G _ _ N hN
  have hr1 : 1 ≤ (2 * N + 1) ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hcl := hNVL G ((2 * N + 1) ^ 2) hr1 (fun g => conjClass_index_le N hN g)
  set t : ℝ := Real.logb 2 (N + 2) with ht
  have hNR : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have ht1 : 1 ≤ t := by
    rw [ht, show (1 : ℝ) = Real.logb 2 2 by simp]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by linarith)
  have hrpos : (0 : ℝ) < ((2 * N + 1) ^ 2 : ℕ) := by positivity
  have hlr : Real.logb 2 (((2 * N + 1) ^ 2 : ℕ)) ≤ 4 * t := by
    have h1 : (((2 * N + 1) ^ 2 : ℕ) : ℝ) = ((2 * (N : ℝ) + 1)) ^ 2 := by push_cast; ring
    rw [h1, Real.logb_pow]
    have h2 : Real.logb 2 (2 * (N : ℝ) + 1) ≤ Real.logb 2 (2 * ((N : ℝ) + 2)) :=
      Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
    have h3 : Real.logb 2 (2 * ((N : ℝ) + 2)) = 1 + t := by
      rw [Real.logb_mul (by norm_num) (by linarith), ht]
      norm_num
    rw [h3] at h2
    push_cast
    linarith
  have hlrpos : 0 ≤ Real.logb 2 (((2 * N + 1) ^ 2 : ℕ)) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hr1)
  calc Real.logb 2 (Nat.card (commutator G))
      ≤ Real.logb 2 ((((2 * N + 1) ^ 2 : ℕ) : ℝ)
          ^ ((3 + 5 * Real.logb 2 (((2 * N + 1) ^ 2 : ℕ))) / 2)) :=
        Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast Nat.card_pos) hcl
    _ = ((3 + 5 * Real.logb 2 (((2 * N + 1) ^ 2 : ℕ))) / 2)
          * Real.logb 2 (((2 * N + 1) ^ 2 : ℕ)) := by
        rw [Real.logb, Real.log_rpow hrpos, Real.logb]
        ring
    _ ≤ ((3 + 5 * (4 * t)) / 2) * (4 * t) := mul_le_mul (by linarith) hlr hlrpos (by linarith)
    _ ≤ 46 * t ^ 2 := by nlinarith

/-! ## 4. Symplectic toolkit -/

/-- A bilinear form with values in `ZMod p`. -/
abbrev AltForm (p : ℕ) [Fact p.Prime] (V : Type*) [AddCommGroup V] [Module (ZMod p) V] :=
  V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

/-- The form is alternating. -/
def IsAltForm (φ : AltForm p V) : Prop := ∀ x : V, φ x x = 0

/-- The radical of a form. -/
def formRadical (φ : AltForm p V) : Submodule (ZMod p) V := LinearMap.ker φ

/-- The rank of a form: the codimension of its radical. -/
noncomputable def formRank (φ : AltForm p V) : ℕ :=
  Module.finrank (ZMod p) V - Module.finrank (ZMod p) (formRadical φ)

/-- A subspace is isotropic when the form vanishes identically on it. -/
def IsIsotropic (φ : AltForm p V) (W : Submodule (ZMod p) V) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W, φ x y = 0

/-- A set is pairwise nonorthogonal (a clique for the form) when the form is nonzero on any two
distinct members. -/
def IsNonorthSet (φ : AltForm p V) (C : Set V) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → φ x y ≠ 0

/-- The orthogonal direct sum `φ₁ ⊥ φ₂`. -/
noncomputable def orthSum {V₁ V₂ : Type*} [AddCommGroup V₁] [Module (ZMod p) V₁]
    [AddCommGroup V₂] [Module (ZMod p) V₂] (φ₁ : AltForm p V₁) (φ₂ : AltForm p V₂) :
    AltForm p (V₁ × V₂) :=
  φ₁.compl₁₂ (LinearMap.fst (ZMod p) V₁ V₂) (LinearMap.fst (ZMod p) V₁ V₂) +
  φ₂.compl₁₂ (LinearMap.snd (ZMod p) V₁ V₂) (LinearMap.snd (ZMod p) V₁ V₂)

theorem orthSum_apply {V₁ V₂ : Type*} [AddCommGroup V₁] [Module (ZMod p) V₁]
    [AddCommGroup V₂] [Module (ZMod p) V₂] (φ₁ : AltForm p V₁) (φ₂ : AltForm p V₂)
    (x y : V₁ × V₂) : orthSum φ₁ φ₂ x y = φ₁ x.1 y.1 + φ₂ x.2 y.2 := rfl

/-- The standard symplectic form on `m` hyperbolic planes. -/
noncomputable def hypForm (p : ℕ) [Fact p.Prime] (m : ℕ) :
    AltForm p (Fin m → ZMod p × ZMod p) :=
  LinearMap.mk₂ (ZMod p) (fun x y => ∑ i, ((x i).1 * (y i).2 - (x i).2 * (y i).1))
    (by intro x y z
        simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring))
    (by intro a x y
        simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring))
    (by intro x y z
        simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring))
    (by intro a x y
        simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring))

theorem hypForm_apply (p : ℕ) [Fact p.Prime] (m : ℕ) (x y : Fin m → ZMod p × ZMod p) :
    hypForm p m x y = ∑ i, ((x i).1 * (y i).2 - (x i).2 * (y i).1) := rfl

theorem hypForm_isAlt (p : ℕ) [Fact p.Prime] (m : ℕ) : IsAltForm (hypForm p m) := by
  intro x
  rw [hypForm_apply]
  exact Finset.sum_eq_zero (fun i _ => by ring)

theorem hypForm_swap (p : ℕ) [Fact p.Prime] (m : ℕ) (x y : Fin m → ZMod p × ZMod p) :
    hypForm p m x y = - hypForm p m y x := by
  rw [hypForm_apply, hypForm_apply, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem finrank_hyp_space (m : ℕ) :
    Module.finrank (ZMod 2) (Fin m → ZMod 2 × ZMod 2) = 2 * m := by
  simp [Module.finrank_pi_fintype, Module.finrank_prod]
  ring

/-- The standard symplectic form is nondegenerate: its radical is trivial. -/
theorem hypForm_orthogonal_top (m : ℕ) :
    LinearMap.BilinForm.orthogonal (hypForm 2 m) ⊤ = ⊥ := by
  ext v
  simp only [Submodule.mem_bot, LinearMap.BilinForm.mem_orthogonal_iff, Submodule.mem_top,
    forall_true_left]
  constructor
  · intro h
    funext i
    have h1 := h (Pi.single i (1, 0))
    have h2 := h (Pi.single i (0, 1))
    rw [hypForm_apply, Finset.sum_eq_single i (fun b _ hb => by simp [Pi.single_eq_of_ne hb])
      (fun hb => absurd (Finset.mem_univ i) hb)] at h1 h2
    simp only [Pi.single_eq_same] at h1 h2
    have e1 : (v i).2 = 0 := by simpa using h1
    have e2 : (v i).1 = 0 := by
      have h3 : -(v i).1 = 0 := by simpa using h2
      simpa using h3
    exact Prod.ext e2 e1
  · rintro rfl n
    rw [hypForm_apply]
    exact Finset.sum_eq_zero (fun i _ => by simp)

/-- An isotropic subspace of the standard symplectic space over `F₂` of dimension `2m` has at
most `2^m` elements. -/
theorem isotropic_card_le (m : ℕ) (W : Submodule (ZMod 2) (Fin m → ZMod 2 × ZMod 2))
    (hW : ∀ x ∈ W, ∀ y ∈ W, hypForm 2 m x y = 0) : Nat.card W ≤ 2 ^ m := by
  have hAlt : (hypForm 2 m).IsAlt := hypForm_isAlt 2 m
  have hrefl : (hypForm 2 m).IsRefl := hAlt.isRefl
  have hle : W ≤ LinearMap.BilinForm.orthogonal (hypForm 2 m) W := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    exact hW n hn x hx
  have hsum := LinearMap.BilinForm.finrank_add_finrank_orthogonal (B := hypForm 2 m) hrefl W
  rw [hypForm_orthogonal_top, finrank_hyp_space] at hsum
  rw [show (W ⊓ (⊥ : Submodule (ZMod 2) (Fin m → ZMod 2 × ZMod 2))) = ⊥ by simp] at hsum
  simp only [finrank_bot, add_zero] at hsum
  have hmono := Submodule.finrank_mono hle
  have hfr : Module.finrank (ZMod 2) W ≤ m := by omega
  rw [(FiniteField.pow_finrank_eq_natCard 2 W).symm]
  exact Nat.pow_le_pow_right (by norm_num) hfr

/-- Over `F₂`, a pairwise nonorthogonal set has at most `dim + 1` elements: removing one member
leaves a linearly independent set, because in characteristic two a vanishing subsum forces a
parity contradiction. -/
theorem card_nonorth_le_finrank_succ {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (f : AltForm 2 W) (hf : IsAltForm f)
    (T : Finset W) (hT : IsNonorthSet f (T : Set W)) :
    T.card ≤ Module.finrank (ZMod 2) W + 1 := by
  rcases T.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
  · simp
  · have hli : LinearIndependent (ZMod 2) (fun x : {x // x ∈ T.erase v} => (x : W)) := by
      rw [linearIndependent_iff']
      intro s g hsum i hi
      by_contra hgi
      set s' := s.filter (fun j => g j ≠ 0) with hs'
      have hmemT : ∀ j : {x // x ∈ T.erase v}, (j : W) ∈ T ∧ (j : W) ≠ v := fun j =>
        ⟨Finset.mem_of_mem_erase j.2, Finset.ne_of_mem_erase j.2⟩
      have hs'sum : ∑ j ∈ s', ((j : W)) = 0 := by
        rw [← hsum, hs', Finset.sum_filter]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        by_cases h : g j = 0
        · simp [h]
        · have h1 : g j = 1 := by revert h; generalize g j = a; revert a; decide
          simp [h1]
      have hcard : ((s'.card : ℕ) : ZMod 2) = 0 := by
        have h0 : f (∑ j ∈ s', ((j : W))) v = 0 := by rw [hs'sum]; simp
        rw [map_sum, LinearMap.sum_apply] at h0
        have hall : ∀ j ∈ s', f (j : W) v = 1 := by
          intro j _
          have h2 : f (j : W) v ≠ 0 := hT _ (hmemT j).1 _ hv (hmemT j).2
          revert h2; generalize f (j : W) v = a; revert a; decide
        rw [Finset.sum_congr rfl hall] at h0
        simpa using h0
      obtain ⟨j0, hj0⟩ : s'.Nonempty := ⟨i, by rw [hs', Finset.mem_filter]; exact ⟨hi, hgi⟩⟩
      have hcard2 : ((s'.card : ℕ) : ZMod 2) = 1 := by
        have h0 : f (∑ j ∈ s', ((j : W))) (j0 : W) = 0 := by rw [hs'sum]; simp
        rw [map_sum, LinearMap.sum_apply, ← Finset.sum_erase_add _ _ hj0, hf] at h0
        have hall : ∀ j ∈ s'.erase j0, f (j : W) (j0 : W) = 1 := by
          intro j hj
          have hne2 : (j : W) ≠ (j0 : W) := fun h => (Finset.ne_of_mem_erase hj) (Subtype.ext h)
          have h2 : f (j : W) (j0 : W) ≠ 0 := hT _ (hmemT j).1 _ (hmemT j0).1 hne2
          revert h2; generalize f (j : W) (j0 : W) = a; revert a; decide
        rw [Finset.sum_congr rfl hall] at h0
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one, add_zero] at h0
        have hc : s'.card = (s'.erase j0).card + 1 := by
          rw [Finset.card_erase_of_mem hj0]
          have := Finset.card_pos.mpr ⟨j0, hj0⟩
          omega
        rw [hc]
        push_cast
        rw [h0]
        ring
      rw [hcard] at hcard2
      exact absurd hcard2 (by decide)
    have hle := LinearIndependent.finset_card_le_finrank hli
    have hcv : (T.erase v).card = T.card - 1 := Finset.card_erase_of_mem hv
    have hpos : 0 < T.card := Finset.card_pos.mpr ⟨v, hv⟩
    omega

/-- Dimension of `m` hyperbolic planes. -/
theorem finrank_hyp_space_gen (p : ℕ) [Fact p.Prime] (m : ℕ) :
    Module.finrank (ZMod p) (Fin m → ZMod p × ZMod p) = 2 * m := by
  simp [Module.finrank_pi_fintype, Module.finrank_prod]
  ring

theorem alt_skew {φ : AltForm p V} (hφ : IsAltForm φ) (x y : V) : φ x y = - φ y x := by
  have h := hφ (x + y)
  simp only [map_add, LinearMap.add_apply, hφ x, hφ y] at h
  have h2 : φ x y + φ y x = 0 := by linear_combination h
  linear_combination h2

/-- The normal form in the degenerate case: a vanishing form. -/
theorem normal_form_of_trivial (φ : AltForm p V) (h : ∀ x y : V, φ x y = 0) :
    ∃ (m : ℕ) (prj : V →ₗ[ZMod p] (Fin m → ZMod p × ZMod p)),
      Function.Surjective prj ∧ LinearMap.ker prj = formRadical φ ∧
      ∀ x y, φ x y = hypForm p m (prj x) (prj y) := by
  refine ⟨0, 0, fun t => ⟨0, Subsingleton.elim _ _⟩, ?_, ?_⟩
  · rw [LinearMap.ker_zero]
    symm
    rw [formRadical, eq_top_iff]
    intro v _
    simp only [LinearMap.mem_ker]
    ext w
    simpa using h v w
  · intro x y
    rw [h x y, hypForm_apply]
    simp

/-- Auxiliary induction for the symplectic normal form. -/
theorem alt_normal_form_aux :
    ∀ (n : ℕ) {U : Type u} [AddCommGroup U] [Module (ZMod p) U] [FiniteDimensional (ZMod p) U]
      (φ : AltForm p U), IsAltForm φ → Module.finrank (ZMod p) U ≤ n →
      ∃ (m : ℕ) (prj : U →ₗ[ZMod p] (Fin m → ZMod p × ZMod p)),
        Function.Surjective prj ∧ LinearMap.ker prj = formRadical φ ∧
        ∀ x y, φ x y = hypForm p m (prj x) (prj y) := by
  intro n
  induction n with
  | zero =>
      intro U _ _ _ φ _ hdim
      have hrank : Module.finrank (ZMod p) U = 0 := Nat.le_zero.mp hdim
      have hsub : Subsingleton U := Module.finrank_zero_iff.mp hrank
      exact normal_form_of_trivial φ (fun x y => by
        rw [Subsingleton.elim x 0]; simp)
  | succ n ih =>
      intro U _ _ _ φ hφ hdim
      by_cases htriv : ∀ x y : U, φ x y = 0
      · exact normal_form_of_trivial φ htriv
      · push Not at htriv
        obtain ⟨x, y0, hxy0⟩ := htriv
        obtain ⟨y, hxy⟩ : ∃ y : U, φ x y = 1 :=
          ⟨(φ x y0)⁻¹ • y0, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hxy0]⟩
        have hyx : φ y x = -1 := by
          have := alt_skew hφ x y
          rw [hxy] at this
          linear_combination this
        obtain ⟨A, hAapp⟩ : ∃ A : U →ₗ[ZMod p] ZMod p, ∀ v, A v = φ v y :=
          ⟨φ.flip y, fun v => rfl⟩
        obtain ⟨Bm, hBapp⟩ : ∃ B : U →ₗ[ZMod p] ZMod p, ∀ v, B v = φ x v :=
          ⟨φ x, fun v => rfl⟩
        obtain ⟨P, hPapp⟩ : ∃ P : U →ₗ[ZMod p] U, ∀ v, P v = v - A v • x - Bm v • y :=
          ⟨LinearMap.id - (LinearMap.smulRight A x) - (LinearMap.smulRight Bm y), by
            intro v; simp⟩
        -- expansion identities
        have expandR : ∀ z v : U, φ z (P v) = φ z v - A v * φ z x - Bm v * φ z y := by
          intro z v
          rw [hPapp]
          simp only [map_sub, map_smul, smul_eq_mul]
        have expandL : ∀ z v : U, φ (P v) z = φ v z - A v * φ x z - Bm v * φ y z := by
          intro z v
          rw [hPapp]
          simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
        have hPx : ∀ v, φ x (P v) = 0 := by
          intro v
          rw [expandR, hφ x, hxy, ← hBapp]
          ring
        have hPy : ∀ v, φ y (P v) = 0 := by
          intro v
          rw [expandR, hyx, hφ y, hAapp v, alt_skew hφ v y]
          ring
        obtain ⟨W, hWmem⟩ : ∃ W : Submodule (ZMod p) U,
            ∀ v, v ∈ W ↔ (φ x v = 0 ∧ φ y v = 0) :=
          ⟨LinearMap.ker (φ x) ⊓ LinearMap.ker (φ y), fun v => Iff.rfl⟩
        have hPW : ∀ v, P v ∈ W := fun v => (hWmem _).mpr ⟨hPx v, hPy v⟩
        obtain ⟨PW, hPWapp⟩ : ∃ PW : U →ₗ[ZMod p] W, ∀ v, (PW v : U) = P v :=
          ⟨P.codRestrict W hPW, fun v => rfl⟩
        obtain ⟨φ', hφ'app⟩ : ∃ φ' : AltForm p W, ∀ a b : W, φ' a b = φ (a : U) (b : U) :=
          ⟨φ.compl₁₂ W.subtype W.subtype, fun a b => rfl⟩
        have hφ'alt : IsAltForm φ' := fun a => by rw [hφ'app]; exact hφ a
        have hkey : ∀ v u : U, φ v u = A v * Bm u - Bm v * A u + φ (P v) (P u) := by
          intro v u
          have e1 : φ (P v) (P u) = φ v (P u) := by
            rw [expandL, hPx, hPy]; ring
          have e2 : φ v (P u) = φ v u + A u * Bm v - Bm u * A v := by
            rw [expandR, hBapp v, alt_skew hφ v x, hAapp v]
            ring
          rw [e1, e2]; ring
        have hWlt : Module.finrank (ZMod p) W ≤ n := by
          have hne : LinearMap.ker (φ x) ≠ ⊤ := by
            intro htop
            have hy : y ∈ LinearMap.ker (φ x) := htop ▸ Submodule.mem_top
            rw [LinearMap.mem_ker] at hy
            rw [hy] at hxy
            exact one_ne_zero hxy.symm
          have h1 : Module.finrank (ZMod p) (LinearMap.ker (φ x)) < Module.finrank (ZMod p) U :=
            Submodule.finrank_lt hne
          have hle : W ≤ LinearMap.ker (φ x) := by
            intro v hv
            exact LinearMap.mem_ker.mpr ((hWmem v).mp hv).1
          have h2 : Module.finrank (ZMod p) W ≤ Module.finrank (ZMod p) (LinearMap.ker (φ x)) :=
            Submodule.finrank_mono hle
          omega
        obtain ⟨m, prjW, hsurj, hker, hform⟩ := ih φ' hφ'alt hWlt
        obtain ⟨prjf, hprjf⟩ : ∃ prjf : U →ₗ[ZMod p] (Fin (m + 1) → ZMod p × ZMod p),
            ∀ v, prjf v = Fin.cons (A v, Bm v) (prjW (PW v)) :=
          ⟨{ toFun := fun v => Fin.cons (A v, Bm v) (prjW (PW v))
             map_add' := by
               intro v u
               funext i
               refine Fin.cases ?_ ?_ i
               · simp
               · intro j
                 simp [Fin.cons_succ]
             map_smul' := by
               intro a v
               funext i
               refine Fin.cases ?_ ?_ i
               · simp
               · intro j
                 simp [Fin.cons_succ] }, fun v => rfl⟩
        have hcoordA : ∀ w' : W, φ (w' : U) y = 0 := by
          intro w'
          rw [alt_skew hφ, ((hWmem _).mp w'.2).2, neg_zero]
        have hcoordB : ∀ w' : W, φ x (w' : U) = 0 := fun w' => ((hWmem _).mp w'.2).1
        refine ⟨m + 1, prjf, ?_, ?_, ?_⟩
        · intro t
          obtain ⟨w, hw⟩ := hsurj (Fin.tail t)
          refine ⟨(t 0).1 • x + (t 0).2 • y + (w : U), ?_⟩
          have hAv : A ((t 0).1 • x + (t 0).2 • y + (w : U)) = (t 0).1 := by
            rw [hAapp]
            simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
              hφ y, hcoordA w, hxy]
            ring
          have hBv : Bm ((t 0).1 • x + (t 0).2 • y + (w : U)) = (t 0).2 := by
            rw [hBapp]
            simp only [map_add, map_smul, smul_eq_mul, hφ x, hxy, hcoordB w]
            ring
          have hPv : PW ((t 0).1 • x + (t 0).2 • y + (w : U)) = w := by
            apply Subtype.ext
            rw [hPWapp, hPapp, hAv, hBv]
            abel
          rw [hprjf, hAv, hBv, hPv, hw, Prod.mk.eta, Fin.cons_self_tail]
        · ext v
          simp only [LinearMap.mem_ker, formRadical]
          constructor
          · intro hv
            rw [hprjf] at hv
            have h0 : (A v, Bm v) = 0 := by
              have := congrFun hv 0
              simpa using this
            have h1 : prjW (PW v) = 0 := by
              funext j
              have := congrFun hv j.succ
              simpa [Fin.cons_succ] using this
            have hA0 : A v = 0 := congrArg Prod.fst h0
            have hB0 : Bm v = 0 := congrArg Prod.snd h0
            have hrad : PW v ∈ formRadical φ' := hker ▸ (LinearMap.mem_ker.mpr h1)
            have hzero : ∀ z : W, φ' (PW v) z = 0 := by
              intro z
              have h2 := LinearMap.mem_ker.mp hrad
              rw [h2]
              rfl
            ext u
            simp only [LinearMap.zero_apply]
            rw [hkey v u, hA0, hB0]
            have h3 : φ (P v) (P u) = 0 := by
              have := hzero (PW u)
              rwa [hφ'app, hPWapp, hPWapp] at this
            rw [h3]
            ring
          · intro hv
            have hall : ∀ u, φ v u = 0 := by
              intro u
              rw [hv]; rfl
            have hA0 : A v = 0 := by rw [hAapp]; exact hall y
            have hB0 : Bm v = 0 := by
              rw [hBapp, alt_skew hφ, hall x, neg_zero]
            have hPv : P v = v := by rw [hPapp, hA0, hB0]; simp
            have h1 : prjW (PW v) = 0 := by
              have hmem : PW v ∈ formRadical φ' := by
                rw [formRadical, LinearMap.mem_ker]
                ext z
                rw [hφ'app, hPWapp, hPv, hall]
                rfl
              rw [← hker] at hmem
              exact LinearMap.mem_ker.mp hmem
            rw [hprjf, hA0, hB0, h1]
            funext i
            refine Fin.cases ?_ ?_ i
            · simp
            · intro j; simp [Fin.cons_succ]
        · intro v u
          rw [hkey v u, hypForm_apply, hprjf, hprjf, Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          have h4 : φ (P v) (P u) = hypForm p m (prjW (PW v)) (prjW (PW u)) := by
            have := hform (PW v) (PW u)
            rwa [hφ'app, hPWapp, hPWapp] at this
          rw [h4, hypForm_apply]

/-- The clean symplectic normal form. -/
theorem alt_normal_form [FiniteDimensional (ZMod p) V] (φ : AltForm p V) (hφ : IsAltForm φ) :
    ∃ (m : ℕ) (prj : V →ₗ[ZMod p] (Fin m → ZMod p × ZMod p)),
      Function.Surjective prj ∧ LinearMap.ker prj = formRadical φ ∧ formRank φ = 2 * m ∧
      ∀ x y, φ x y = hypForm p m (prj x) (prj y) := by
  obtain ⟨m, prj, hsurj, hker, hform⟩ :=
    alt_normal_form_aux (Module.finrank (ZMod p) V) φ hφ le_rfl
  refine ⟨m, prj, hsurj, hker, ?_, hform⟩
  have hrange : LinearMap.range prj = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have h1 : Module.finrank (ZMod p) (LinearMap.range prj) + Module.finrank (ZMod p) (LinearMap.ker prj)
      = Module.finrank (ZMod p) V := LinearMap.finrank_range_add_finrank_ker prj
  rw [hrange, finrank_top, finrank_hyp_space_gen, hker] at h1
  rw [formRank]
  omega

theorem finrank_galoisField (p n : ℕ) [Fact p.Prime] [NeZero n] :
    Module.finrank (ZMod p) (GaloisField p n) = n := by
  have : Fintype (GaloisField p n) := Fintype.ofFinite _
  have h1 : Fintype.card (GaloisField p n)
      = Fintype.card (ZMod p) ^ Module.finrank (ZMod p) (GaloisField p n) :=
    Module.card_eq_pow_finrank
  have h2 : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n (NeZero.ne n)
  rw [Nat.card_eq_fintype_card] at h2
  rw [ZMod.card] at h1
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le (h1.symm.trans h2)

/-- The trace form on `K × K`, `K` a finite extension of `F_p`. -/
noncomputable def traceSymp (p n : ℕ) [Fact p.Prime] [NeZero n] :
    AltForm p (GaloisField p n × GaloisField p n) :=
  LinearMap.mk₂ (ZMod p)
    (fun a b => Algebra.trace (ZMod p) (GaloisField p n) (a.1 * b.2 - a.2 * b.1))
    (by intro a a' b
        simp only [Prod.fst_add, Prod.snd_add]
        rw [← map_add]
        congr 1
        ring)
    (by intro c a b
        simp only [Prod.smul_fst, Prod.smul_snd]
        rw [← map_smul]
        congr 1
        simp only [smul_mul_assoc, smul_sub])
    (by intro a b b'
        simp only [Prod.fst_add, Prod.snd_add]
        rw [← map_add]
        congr 1
        ring)
    (by intro c a b
        simp only [Prod.smul_fst, Prod.smul_snd]
        rw [← map_smul]
        congr 1
        simp only [mul_smul_comm, smul_sub])

theorem traceSymp_apply (p n : ℕ) [Fact p.Prime] [NeZero n]
    (a b : GaloisField p n × GaloisField p n) :
    traceSymp p n a b = Algebra.trace (ZMod p) (GaloisField p n) (a.1 * b.2 - a.2 * b.1) := rfl

theorem traceSymp_isAlt (p n : ℕ) [Fact p.Prime] [NeZero n] : IsAltForm (traceSymp p n) := by
  intro a
  rw [traceSymp_apply]
  simp [mul_comm]

theorem traceSymp_radical (p n : ℕ) [Fact p.Prime] [NeZero n] :
    formRadical (traceSymp p n) = ⊥ := by
  have hnd := traceForm_nondegenerate (ZMod p) (GaloisField p n)
  rw [formRadical, eq_bot_iff]
  intro a ha
  rw [LinearMap.mem_ker] at ha
  have hall : ∀ b, traceSymp p n a b = 0 := by
    intro b
    rw [ha]; rfl
  have h1 : a.1 = 0 := by
    refine hnd.1 a.1 (fun y => ?_)
    have := hall (0, y)
    rw [traceSymp_apply] at this
    simpa [Algebra.traceForm_apply] using this
  have h2 : a.2 = 0 := by
    refine hnd.1 a.2 (fun y => ?_)
    have := hall (y, 0)
    rw [traceSymp_apply] at this
    simp only [mul_zero, zero_sub, map_neg, neg_eq_zero] at this
    simpa [Algebra.traceForm_apply, mul_comm] using this
  simp only [Submodule.mem_bot]
  exact Prod.ext h1 h2

/-- The lines of the classical symplectic spread on `K × K`. -/
theorem traceSymp_spread (p n : ℕ) [Fact p.Prime] [NeZero n] :
    ∃ F : Finset (Submodule (ZMod p) (GaloisField p n × GaloisField p n)),
      F.card ≤ p ^ n + 1 ∧ (∀ W ∈ F, IsIsotropic (traceSymp p n) W) ∧
      ∀ v, ∃ W ∈ F, v ∈ W := by
  classical
  have : Fintype (GaloisField p n) := Fintype.ofFinite _
  set K := GaloisField p n
  set line : K → Submodule (ZMod p) (K × K) := fun t =>
    LinearMap.range ((LinearMap.id.prod (LinearMap.mulLeft (ZMod p) t) :
      K →ₗ[ZMod p] K × K)) with hline
  set vert : Submodule (ZMod p) (K × K) :=
    LinearMap.range ((0 : K →ₗ[ZMod p] K).prod LinearMap.id) with hvert
  have hmemline : ∀ (t : K) (v : K × K), v ∈ line t ↔ v.2 = t * v.1 := by
    intro t v
    constructor
    · rintro ⟨x, rfl⟩
      simp
    · intro h
      refine ⟨v.1, ?_⟩
      simp only [LinearMap.prod_apply, LinearMap.id_coe]
      exact Prod.ext rfl h.symm
  have hmemvert : ∀ v : K × K, v ∈ vert ↔ v.1 = 0 := by
    intro v
    constructor
    · rintro ⟨x, rfl⟩
      simp
    · intro h
      exact ⟨v.2, Prod.ext (by simpa using h.symm) rfl⟩
  refine ⟨insert vert (Finset.univ.image line), ?_, ?_, ?_⟩
  · calc (insert vert (Finset.univ.image line)).card
        ≤ (Finset.univ.image line).card + 1 := Finset.card_insert_le _ _
      _ ≤ (Finset.univ : Finset K).card + 1 := by
          exact Nat.add_le_add_right (Finset.card_image_le) 1
      _ = p ^ n + 1 := by
          rw [Finset.card_univ]
          have h2 : Nat.card K = p ^ n := GaloisField.card p n (NeZero.ne n)
          rw [Nat.card_eq_fintype_card] at h2
          rw [h2]
  · intro W hW
    rcases Finset.mem_insert.mp hW with rfl | hW
    · intro x hx y hy
      rw [traceSymp_apply, (hmemvert x).mp hx, (hmemvert y).mp hy]
      simp
    · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hW
      intro x hx y hy
      rw [traceSymp_apply, (hmemline t x).mp hx, (hmemline t y).mp hy]
      have : x.1 * (t * y.1) - t * x.1 * y.1 = 0 := by ring
      rw [this, map_zero]
  · intro v
    rcases eq_or_ne v.1 0 with h | h
    · exact ⟨vert, Finset.mem_insert_self _ _, (hmemvert v).mpr h⟩
    · refine ⟨line (v.2 / v.1), Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩), ?_⟩
      rw [hmemline, div_mul_cancel₀ _ h]

/-- A symplectic spread of the standard model: `p^m + 1` isotropic subspaces covering the
space of `m` hyperbolic planes. -/
theorem hyp_spread (p : ℕ) [Fact p.Prime] (m : ℕ) :
    ∃ F : Finset (Submodule (ZMod p) (Fin m → ZMod p × ZMod p)),
      F.card ≤ p ^ m + 1 ∧ (∀ W ∈ F, IsIsotropic (hypForm p m) W) ∧ ∀ v, ∃ W ∈ F, v ∈ W := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨{⊥}, by simp, ?_, ?_⟩
    · intro W hW x _ y _
      rw [hypForm_apply]
      simp
    · intro v
      refine ⟨⊥, by simp, ?_⟩
      have : v = 0 := Subsingleton.elim _ _
      simp [this]
  · have : NeZero m := ⟨by omega⟩
    have : Fintype (GaloisField p m) := Fintype.ofFinite _
    have : FiniteDimensional (ZMod p) (GaloisField p m × GaloisField p m) :=
      Module.Finite.of_finite
    obtain ⟨m', prj, hsurj, hker, hrank, hform⟩ :=
      alt_normal_form (traceSymp p m) (traceSymp_isAlt p m)
    have hdim : Module.finrank (ZMod p) (GaloisField p m × GaloisField p m) = 2 * m := by
      rw [Module.finrank_prod, finrank_galoisField]
      ring
    have hmm : m' = m := by
      have h1 : formRank (traceSymp p m) = 2 * m := by
        rw [formRank, traceSymp_radical, hdim]
        simp
      omega
    subst hmm
    obtain ⟨F, hcard, hiso, hcover⟩ := traceSymp_spread p m'
    refine ⟨F.image (Submodule.map prj), ?_, ?_, ?_⟩
    · exact le_trans Finset.card_image_le hcard
    · intro W hW
      obtain ⟨W₀, hW₀, rfl⟩ := Finset.mem_image.mp hW
      rintro x hx y hy
      obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
      obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hy
      rw [← hform]
      exact hiso W₀ hW₀ a ha b hb
    · intro v
      obtain ⟨a, rfl⟩ := hsurj v
      obtain ⟨W₀, hW₀, ha⟩ := hcover a
      exact ⟨Submodule.map prj W₀, Finset.mem_image_of_mem _ hW₀, Submodule.mem_map_of_mem ha⟩


/-- **Lemma 4.1** (Spread cover): a space carrying an alternating form of rank `2m` is the union
of at most `p^m + 1` isotropic subspaces. -/
theorem spread_cover [FiniteDimensional (ZMod p) V] (φ : AltForm p V) (hφ : IsAltForm φ)
    (m : ℕ) (hm : formRank φ = 2 * m) :
    ∃ F : Finset (Submodule (ZMod p) V), F.card ≤ p ^ m + 1 ∧ (∀ W ∈ F, IsIsotropic φ W) ∧
      ∀ v : V, ∃ W ∈ F, v ∈ W := by
  classical
  obtain ⟨m₀, prj, hsurj, hker, hrank, hform⟩ := alt_normal_form φ hφ
  have hmm : m₀ = m := by omega
  subst hmm
  obtain ⟨F, hcard, hiso, hcover⟩ := hyp_spread p m₀
  refine ⟨F.image (Submodule.comap prj), ?_, ?_, ?_⟩
  · exact le_trans Finset.card_image_le hcard
  · intro W hW
    obtain ⟨W₀, hW₀, rfl⟩ := Finset.mem_image.mp hW
    intro x hx y hy
    rw [hform]
    exact hiso W₀ hW₀ (prj x) (Submodule.mem_comap.mp hx) (prj y) (Submodule.mem_comap.mp hy)
  · intro v
    obtain ⟨W₀, hW₀, hv⟩ := hcover (prj v)
    exact ⟨Submodule.comap prj W₀, Finset.mem_image_of_mem _ hW₀, Submodule.mem_comap.mpr hv⟩

/-- **Definition 4.2**: the clique-credit constant `κ_p`. -/
noncomputable def kappa (p : ℕ) : ℝ := if p = 2 then 1 else if p = 3 then 2 else (p : ℝ) / 2

/-- **Definition 4.2**: the additive loss `c_p`. -/
noncomputable def cc (p : ℕ) : ℝ := if p = 3 then 2 else 0

/-- The exponential coefficient `α_p = log₂ p / (2 κ_p)` of Theorem 6.1. -/
noncomputable def alphaP (p : ℕ) : ℝ := Real.logb 2 p / (2 * kappa p)

theorem kappa_pos {q : ℕ} (hq : 2 ≤ q) : 0 < kappa q := by
  unfold kappa
  split_ifs with h2 h3
  · norm_num
  · norm_num
  · have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith

/-- **Lemma 4.3** (Orthogonal-anchor composition). -/
theorem orth_anchor_comp {V₁ V₂ : Type*} [AddCommGroup V₁] [Module (ZMod p) V₁]
    [AddCommGroup V₂] [Module (ZMod p) V₂] (f₁ : AltForm p V₁) (f₂ : AltForm p V₂)
    (hf₁ : IsAltForm f₁) (C₁ : Finset V₁) (C₂ : Finset V₂) (u₁ : V₁) (u₂ : V₂)
    (hu₁ : u₁ ∈ C₁) (hu₂ : u₂ ∈ C₂)
    (h₁ : IsNonorthSet f₁ (C₁ : Set V₁)) (h₂ : IsNonorthSet f₂ (C₂ : Set V₂)) :
    ∃ C : Finset (V₁ × V₂), IsNonorthSet (orthSum f₁ f₂) (C : Set (V₁ × V₂)) ∧
      C.card = C₁.card + C₂.card - 1 ∧ (u₁, u₂) ∈ C := by
  classical
  refine ⟨(C₁.erase u₁).image (fun x => (x, (0 : V₂))) ∪ C₂.image (fun v => (u₁, v)), ?_, ?_, ?_⟩
  · rintro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_image, Finset.mem_erase] at hx hy
    rw [orthSum_apply]
    rcases hx with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ <;> rcases hy with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩
    · simp only [map_zero, add_zero]
      exact h₁ a ha.2 b hb.2 (by rintro rfl; exact hxy rfl)
    · simp only [map_zero, LinearMap.zero_apply, add_zero]
      exact h₁ a ha.2 u₁ hu₁ ha.1
    · simp only [map_zero, add_zero]
      exact h₁ u₁ hu₁ b hb.2 (fun h => hb.1 h.symm)
    · simp only [hf₁ u₁, zero_add]
      exact h₂ a ha b hb (by rintro rfl; exact hxy rfl)
  · have hdisj : Disjoint ((C₁.erase u₁).image (fun x => (x, (0 : V₂))))
        (C₂.image (fun v => (u₁, v))) := by
      rw [Finset.disjoint_left]
      rintro x hx hy
      simp only [Finset.mem_image, Finset.mem_erase] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, _, hab⟩ := hy
      exact ha.1 (congrArg Prod.fst hab).symm
    rw [Finset.card_union_of_disjoint hdisj]
    have e1 : ((C₁.erase u₁).image (fun x => (x, (0 : V₂)))).card = C₁.card - 1 := by
      rw [Finset.card_image_of_injective _ (fun a b hab => (Prod.mk.injEq _ _ _ _ ▸ hab).1),
        Finset.card_erase_of_mem hu₁]
    have e2 : (C₂.image (fun v => (u₁, v))).card = C₂.card :=
      Finset.card_image_of_injective _ (fun a b hab => (Prod.mk.injEq _ _ _ _ ▸ hab).2)
    rw [e1, e2]
    have : 1 ≤ C₁.card := Finset.card_pos.mpr ⟨u₁, hu₁⟩
    omega
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u₂, hu₂, rfl⟩)

/-- The thirteen projective points of `F₃⁶` used in Lemma 4.4. -/
def pts13 : Fin 13 → (Fin 3 → ZMod 3 × ZMod 3) :=
  ![![(1,2),(0,2),(1,1)], ![(0,1),(1,0),(0,2)], ![(0,1),(0,1),(0,0)], ![(0,1),(1,2),(2,1)],
    ![(1,2),(1,0),(2,0)], ![(1,1),(0,1),(2,2)], ![(1,0),(0,1),(2,0)], ![(1,0),(1,1),(2,1)],
    ![(1,1),(1,0),(0,1)], ![(1,2),(0,0),(2,1)], ![(1,0),(0,1),(1,1)], ![(1,0),(1,1),(1,1)],
    ![(1,2),(0,1),(1,0)]]

/-- The explicit `p = 3` computation inside Lemma 4.4: the thirteen listed points of a rank-six
symplectic space over `F₃` are pairwise nonorthogonal. -/
theorem pts13_pairwise_nonorth : ∀ i j : Fin 13, i ≠ j → hypForm 3 3 (pts13 i) (pts13 j) ≠ 0 := by
  decide

/-- There is a pairwise nonorthogonal set of size at least `k`, containing a distinguished
element, in the standard symplectic space of `m` hyperbolic planes over `F_p`. -/
def HasClique (p : ℕ) [Fact p.Prime] (m k : ℕ) : Prop :=
  ∃ (C : Finset (Fin m → ZMod p × ZMod p)) (u : Fin m → ZMod p × ZMod p),
    IsNonorthSet (hypForm p m) (C : Set (Fin m → ZMod p × ZMod p)) ∧ u ∈ C ∧ k ≤ C.card

theorem hypForm_append {m₁ m₂ : ℕ} (x₁ y₁ : Fin m₁ → ZMod p × ZMod p)
    (x₂ y₂ : Fin m₂ → ZMod p × ZMod p) :
    hypForm p (m₁ + m₂) (Fin.append x₁ x₂) (Fin.append y₁ y₂)
      = hypForm p m₁ x₁ y₁ + hypForm p m₂ x₂ y₂ := by
  rw [hypForm_apply, hypForm_apply, hypForm_apply, Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]


theorem hypForm_zero_right {m : ℕ} (x : Fin m → ZMod p × ZMod p) : hypForm p m x 0 = 0 := by
  rw [hypForm_apply]
  exact Finset.sum_eq_zero (fun i _ => by simp)

theorem hypForm_zero_left {m : ℕ} (x : Fin m → ZMod p × ZMod p) : hypForm p m 0 x = 0 := by
  rw [hypForm_apply]
  exact Finset.sum_eq_zero (fun i _ => by simp)

omit [Fact p.Prime] in
theorem append_left_inj {m₁ m₂ : ℕ} {a a' : Fin m₁ → ZMod p × ZMod p}
    {b b' : Fin m₂ → ZMod p × ZMod p} (h : Fin.append a b = Fin.append a' b') : a = a' := by
  funext i
  have := congrFun h (Fin.castAdd m₂ i)
  simpa [Fin.append_left] using this

omit [Fact p.Prime] in
theorem append_right_inj {m₁ m₂ : ℕ} {a a' : Fin m₁ → ZMod p × ZMod p}
    {b b' : Fin m₂ → ZMod p × ZMod p} (h : Fin.append a b = Fin.append a' b') : b = b' := by
  funext i
  have := congrFun h (Fin.natAdd m₁ i)
  simpa [Fin.append_right] using this

/-- Orthogonal-anchor composition in the standard model. -/
theorem clique_append {m₁ m₂ k₁ k₂ : ℕ} (h₁ : HasClique p m₁ k₁) (h₂ : HasClique p m₂ k₂) :
    HasClique p (m₁ + m₂) (k₁ + k₂ - 1) := by
  classical
  obtain ⟨C₁, u₁, hC₁, hu₁, hk₁⟩ := h₁
  obtain ⟨C₂, u₂, hC₂, hu₂, hk₂⟩ := h₂
  refine ⟨((C₁.erase u₁).image (fun a => Fin.append a (0 : Fin m₂ → ZMod p × ZMod p))) ∪
      (C₂.image (fun c => Fin.append u₁ c)), Fin.append u₁ u₂, ?_, ?_, ?_⟩
  · rintro x hx y hy hxy
    simp only [Finset.coe_union, Set.mem_union, Finset.coe_image, Set.mem_image,
      Finset.mem_coe, Finset.mem_erase] at hx hy
    rcases hx with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ <;> rcases hy with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩
    · rw [hypForm_append, hypForm_zero_right, add_zero]
      exact hC₁ a ha.2 b hb.2 (by rintro rfl; exact hxy rfl)
    · rw [hypForm_append, hypForm_zero_left, add_zero]
      exact hC₁ a ha.2 u₁ hu₁ ha.1
    · rw [hypForm_append, hypForm_zero_right, add_zero]
      exact hC₁ u₁ hu₁ b hb.2 (fun h => hb.1 h.symm)
    · rw [hypForm_append, hypForm_isAlt p m₁ u₁, zero_add]
      exact hC₂ a ha b hb (by rintro rfl; exact hxy rfl)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u₂, hu₂, rfl⟩)
  · have hdisj : Disjoint ((C₁.erase u₁).image (fun a => Fin.append a (0 : Fin m₂ → ZMod p × ZMod p)))
        (C₂.image (fun c => Fin.append u₁ c)) := by
      rw [Finset.disjoint_left]
      rintro z hz hz'
      simp only [Finset.mem_image, Finset.mem_erase] at hz hz'
      obtain ⟨a, ha, rfl⟩ := hz
      obtain ⟨c, _, hc⟩ := hz'
      exact ha.1 (append_left_inj hc.symm)
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (fun a a' h => append_left_inj h),
      Finset.card_image_of_injective _ (fun c c' h => append_right_inj h),
      Finset.card_erase_of_mem hu₁]
    have : 1 ≤ C₁.card := Finset.card_pos.mpr ⟨u₁, hu₁⟩
    omega

theorem hasClique_zero : HasClique p 0 1 := by
  refine ⟨{0}, 0, ?_, by simp, by simp⟩
  intro x hx y hy hxy
  simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx hy
  exact absurd (hx.trans hy.symm) hxy

/-- A hyperbolic plane contains a clique of size `p + 1`. -/
theorem hasClique_one : HasClique p 1 (p + 1) := by
  classical
  refine ⟨(Finset.univ.image (fun l : ZMod p => (fun _ : Fin 1 => ((1 : ZMod p), l)))) ∪
      {fun _ : Fin 1 => ((0 : ZMod p), (1 : ZMod p))},
      (fun _ : Fin 1 => ((0 : ZMod p), (1 : ZMod p))), ?_, ?_, ?_⟩
  · rintro x hx y hy hxy
    simp only [Finset.coe_union, Set.mem_union, Finset.coe_image, Set.mem_image, Finset.mem_coe,
      Finset.mem_univ, true_and, Finset.coe_singleton, Set.mem_singleton_iff] at hx hy
    rw [hypForm_apply, Fin.sum_univ_one]
    rcases hx with ⟨l, rfl⟩ | rfl <;> rcases hy with ⟨l', rfl⟩ | rfl
    · simp only
      intro hc
      apply hxy
      funext i
      have : l = l' := by
        have : l' - l = 0 := by linear_combination hc
        linear_combination -this
      rw [this]
    · simp
    · simp
    · exact absurd rfl hxy
  · exact Finset.mem_union_right _ (by simp)
  · have hinj : Function.Injective (fun l : ZMod p => (fun _ : Fin 1 => ((1 : ZMod p), l))) := by
      intro l l' h
      have := congrFun h 0
      exact (Prod.mk.injEq _ _ _ _ ▸ this).2
    have hnotmem : (fun _ : Fin 1 => ((0 : ZMod p), (1 : ZMod p))) ∉
        (Finset.univ.image (fun l : ZMod p => (fun _ : Fin 1 => ((1 : ZMod p), l)))) := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
      intro l hl
      have := congrFun hl 0
      have h0 : (1 : ZMod p) = 0 := (Prod.mk.injEq _ _ _ _ ▸ this).1
      exact one_ne_zero h0
    rw [Finset.union_comm, Finset.card_union_of_disjoint (by
        simp [hnotmem]),
      Finset.card_image_of_injective _ hinj, Finset.card_univ, ZMod.card]
    simp

/-- The generic clique: `p m + 1` pairwise nonorthogonal vectors in rank `2m`. -/
theorem hasClique_generic (m : ℕ) : HasClique p m (p * m + 1) := by
  induction m with
  | zero => simpa using (hasClique_zero : HasClique p 0 1)
  | succ m ih =>
      have h := clique_append ih (hasClique_one (p := p))
      have he : p * m + 1 + (p + 1) - 1 = p * (m + 1) + 1 := by ring_nf; omega
      rw [he] at h
      exact h

theorem hasClique_mono {m k k' : ℕ} (h : HasClique p m k) (hk : k' ≤ k) : HasClique p m k' := by
  obtain ⟨C, u, hC, hu, hcard⟩ := h
  exact ⟨C, u, hC, hu, le_trans hk hcard⟩


theorem hasClique_pts13 : HasClique 3 3 13 := by
  classical
  refine ⟨Finset.univ.image pts13, pts13 0, ?_, by simp, ?_⟩
  · rintro x hx y hy hxy
    simp only [Finset.coe_image, Set.mem_image, true_and,
      Finset.coe_univ, Set.mem_univ] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    exact pts13_pairwise_nonorth i j (fun h => hxy (by rw [h]))
  · have hinj : Function.Injective pts13 := by
      intro i j hij
      by_contra hne
      exact pts13_pairwise_nonorth i j hne (by rw [hij]; exact hypForm_isAlt 3 3 _)
    rw [Finset.card_image_of_injective _ hinj]
    simp

/-- For `p = 3` the thirteen-point block gives clique credit `4m - 1` in rank `2m`. -/
theorem hasClique_three : ∀ m : ℕ, HasClique 3 m (4 * m - 1) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      match m, ih with
      | 0, _ => exact hasClique_mono (hasClique_zero (p := 3)) (by omega)
      | 1, _ => exact hasClique_mono (hasClique_one (p := 3)) (by omega)
      | 2, _ =>
          have h := clique_append (hasClique_one (p := 3)) (hasClique_one (p := 3))
          exact hasClique_mono h (by omega)
      | (k + 3), ih =>
          have hk := ih k (by omega)
          have h := clique_append hasClique_pts13 hk
          have he : (3 : ℕ) + k = k + 3 := by omega
          rw [he] at h
          exact hasClique_mono h (by omega)


/-- Transport a clique of the standard model along a surjection realising the form. -/
theorem clique_lift (φ : AltForm p V) {m k : ℕ}
    (prj : V →ₗ[ZMod p] (Fin m → ZMod p × ZMod p)) (hsurj : Function.Surjective prj)
    (hform : ∀ x y, φ x y = hypForm p m (prj x) (prj y)) (h : HasClique p m k) :
    ∃ C : Finset V, IsNonorthSet φ (C : Set V) ∧ k ≤ C.card ∧ 1 ≤ C.card := by
  classical
  obtain ⟨D, u, hD, hu, hcard⟩ := h
  choose s hs using hsurj
  have hsinj : Function.Injective s := by
    intro t t' h
    rw [← hs t, ← hs t', h]
  refine ⟨D.image s, ?_, ?_, ?_⟩
  · rintro x hx y hy hxy
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
    obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨t', ht', rfl⟩ := hy
    rw [hform, hs, hs]
    exact hD t ht t' ht' (fun h => hxy (by rw [h]))
  · rwa [Finset.card_image_of_injective _ hsinj]
  · rw [Finset.card_image_of_injective _ hsinj]
    exact Finset.card_pos.mpr ⟨u, hu⟩


/-- **Lemma 4.4** (Scalar clique credit). -/
theorem scalar_clique_credit [FiniteDimensional (ZMod p) V] (φ : AltForm p V)
    (hφ : IsAltForm φ) :
    ∃ C : Finset V, IsNonorthSet φ (C : Set V) ∧
      (C.card : ℝ) - 1 ≥ kappa p * (formRank φ : ℝ) - cc p := by
  obtain ⟨m, prj, hsurj, hker, hrank, hform⟩ := alt_normal_form φ hφ
  have hprime : p.Prime := Fact.out
  rcases eq_or_ne p 2 with rfl | h2
  · obtain ⟨C, hC, hcard, _⟩ := clique_lift φ prj hsurj hform (hasClique_generic (p := 2) m)
    refine ⟨C, hC, ?_⟩
    have h1 : ((2 * m + 1 : ℕ) : ℝ) ≤ (C.card : ℝ) := by exact_mod_cast hcard
    rw [hrank, kappa, cc]
    norm_num at h1 ⊢
    linarith
  rcases eq_or_ne p 3 with rfl | h3
  · obtain ⟨C, hC, hcard, hpos⟩ := clique_lift φ prj hsurj hform (hasClique_three m)
    refine ⟨C, hC, ?_⟩
    rw [hrank, kappa, cc]
    norm_num
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have h1 : (1 : ℝ) ≤ (C.card : ℝ) := by exact_mod_cast hpos
      norm_num
      linarith
    · have h1 : ((4 * m - 1 : ℕ) : ℝ) ≤ (C.card : ℝ) := by exact_mod_cast hcard
      have h2 : ((4 * m - 1 : ℕ) : ℝ) = 4 * (m : ℝ) - 1 := by
        have : (1 : ℕ) ≤ 4 * m := by omega
        push_cast [Nat.cast_sub this]
        ring
      rw [h2] at h1
      linarith
  · have h5 : 5 ≤ p := by
      have := hprime.two_le
      have h4 : p ≠ 4 := by rintro rfl; norm_num at hprime
      omega
    obtain ⟨C, hC, hcard, _⟩ := clique_lift φ prj hsurj hform (hasClique_generic (p := p) m)
    refine ⟨C, hC, ?_⟩
    have h1 : ((p * m + 1 : ℕ) : ℝ) ≤ (C.card : ℝ) := by exact_mod_cast hcard
    push_cast at h1
    rw [hrank, kappa, cc, ite_eq_right h2, ite_eq_right h3, ite_eq_right h3]
    push_cast
    linarith

/-- An elementary estimate used for the odd primes in Remark 4.5. -/
theorem sq_lt_two_pow_of_five_le : ∀ n : ℕ, 5 ≤ n → n ^ 2 < 2 ^ n := by
  intro n hn
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 5 with hk | hk
    · interval_cases k
      · omega
      · omega
      · omega
      · omega
      · norm_num
    · have h1 := ih hk
      have h2 : (k + 1) ^ 2 ≤ 2 * k ^ 2 := by nlinarith
      calc (k + 1) ^ 2 ≤ 2 * k ^ 2 := h2
        _ < 2 * 2 ^ k := Nat.mul_lt_mul_of_pos_left h1 (by norm_num)
        _ = 2 ^ (k + 1) := by ring

theorem alphaP_two : alphaP 2 = 1 / 2 := by
  simp [alphaP, kappa, Real.logb_self_eq_one]

set_option exponentiation.threshold 400 in
/-- **Remark 4.5**: `α₃ = (log₂ 3)/4 < 0.397`. -/
theorem alphaP_three_lt : alphaP 3 < 0.397 := by
  have h3 : (3 : ℕ) ^ 250 < 2 ^ 397 := by decide
  have h3' : (3 : ℝ) ^ (250 : ℕ) < (2 : ℝ) ^ (397 : ℕ) := by exact_mod_cast h3
  have hlog : (250 : ℝ) * Real.log 3 < 397 * Real.log 2 := by
    have := Real.log_lt_log (by positivity) h3'
    rwa [Real.log_pow, Real.log_pow] at this
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hb : Real.logb 2 3 < 1.588 := by
    rw [Real.logb, div_lt_iff₀ hlog2]
    nlinarith
  have hk : kappa 3 = 2 := by norm_num [kappa]
  rw [alphaP, hk]
  norm_num
  linarith

/-- **Remark 4.5**: `α_p = (log₂ p)/p < 1/2` for `p ≥ 5`. -/
theorem alphaP_lt_half_of_five_le {q : ℕ} (h5 : 5 ≤ q) : alphaP q < 1 / 2 := by
  have hq2 : q ≠ 2 := by omega
  have hq3 : q ≠ 3 := by omega
  have hk : kappa q = (q : ℝ) / 2 := by simp [kappa, hq2, hq3]
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    have : (0 : ℕ) < q := by omega
    exact_mod_cast this
  have hpow : (q : ℝ) ^ (2 : ℕ) < (2 : ℝ) ^ (q : ℕ) := by
    exact_mod_cast sq_lt_two_pow_of_five_le q h5
  have hlog : 2 * Real.log q < q * Real.log 2 := by
    have := Real.log_lt_log (by positivity) hpow
    rwa [Real.log_pow, Real.log_pow] at this
  rw [alphaP, hk, show (2 : ℝ) * ((q : ℝ) / 2) = (q : ℝ) by ring, Real.logb, div_div,
    div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- **Remark 4.5**: `α_p ≤ 1/2` for every prime, with equality only at `p = 2`. -/
theorem alphaP_le_half {q : ℕ} (hq : q.Prime) : alphaP q ≤ 1 / 2 := by
  rcases eq_or_ne q 2 with rfl | h2
  · exact le_of_eq alphaP_two
  rcases eq_or_ne q 3 with rfl | h3
  · linarith [alphaP_three_lt]
  have h4 : q ≠ 4 := by
    rintro rfl
    norm_num at hq
  have h5 : 5 ≤ q := by
    have := hq.two_le
    omega
  exact le_of_lt (alphaP_lt_half_of_five_le h5)

/-! ### 4.1 The extraspecial lower bound -/

/-- The symplectic description of an extraspecial `2`-group of order `2^{1+2m}`: the central
quotient is a `2m`-dimensional symplectic space over `F₂`, commutation corresponding to the
symplectic form. -/
structure ExtraspecialData (m : ℕ) (E : Type) [Group E] : Type where
  /-- The projection to the central quotient, viewed as a symplectic space. -/
  pi : E → (Fin m → ZMod 2 × ZMod 2)
  /-- `pi` is a homomorphism. -/
  pi_mul : ∀ x y : E, pi (x * y) = pi x + pi y
  /-- `pi` is surjective. -/
  pi_surj : Function.Surjective pi
  /-- The kernel of `pi` is the centre. -/
  pi_ker : ∀ x : E, pi x = 0 ↔ x ∈ Subgroup.center E
  /-- The centre has order two. -/
  card_center : Nat.card (Subgroup.center E) = 2
  /-- Commutation is detected by the symplectic form. -/
  comm_iff : ∀ x y : E, (⁅x, y⁆ = 1 ↔ hypForm 2 m (pi x) (pi y) = 0)

/-- Existence of extraspecial `2`-groups of order `2^{1+2m}` (classical). -/
def ExtraspecialExists : Prop :=
  ∀ m : ℕ, ∃ (E : Type) (inst : Group E), Finite E ∧ Nonempty (@ExtraspecialData m E inst)

/-- An explicit family of `2m + 1` pairwise nonorthogonal vectors of the standard symplectic
space over `F₂`: the `k`-th vector vanishes on the hyperbolic planes before `⌊(k-1)/2⌋`, equals
`(0,1)` or `(1,1)` on that plane, and equals `(1,0)` on the later planes. -/
def cliqueVec (m : ℕ) (k : ℕ) : Fin m → ZMod 2 × ZMod 2 := fun i =>
  if 2 * (i : ℕ) + 2 < k then (0, 0)
  else if 2 * (i : ℕ) + 2 = k then (1, 1)
  else if 2 * (i : ℕ) + 1 = k then (0, 1)
  else (1, 0)

theorem cliqueVec_pair (m k l : ℕ) (hkl : k < l) (hl : l ≤ 2 * m) :
    hypForm 2 m (cliqueVec m k) (cliqueVec m l) = 1 := by
  have hm : 0 < m := by omega
  have hi0 : (l - 1) / 2 < m := by omega
  rw [hypForm_apply, Finset.sum_eq_single (⟨(l - 1) / 2, hi0⟩ : Fin m)]
  · rcases Nat.even_or_odd l with he | ho
    · have hpar : l % 2 = 0 := Nat.even_iff.mp he
      have h1 : cliqueVec m l ⟨(l - 1) / 2, hi0⟩ = (1, 1) := by
        simp only [cliqueVec]
        rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      rcases eq_or_ne k (2 * ((l - 1) / 2) + 1) with hk | hk
      · have h2 : cliqueVec m k ⟨(l - 1) / 2, hi0⟩ = (0, 1) := by
          simp only [cliqueVec]
          rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
        rw [h1, h2]; decide
      · have h2 : cliqueVec m k ⟨(l - 1) / 2, hi0⟩ = (1, 0) := by
          simp only [cliqueVec]
          rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
        rw [h1, h2]; decide
    · have hpar : l % 2 = 1 := Nat.odd_iff.mp ho
      have h1 : cliqueVec m l ⟨(l - 1) / 2, hi0⟩ = (0, 1) := by
        simp only [cliqueVec]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
      have h2 : cliqueVec m k ⟨(l - 1) / 2, hi0⟩ = (1, 0) := by
        simp only [cliqueVec]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      rw [h1, h2]; decide
  · intro i _ hne
    have hne' : (i : ℕ) ≠ (l - 1) / 2 := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hne' with h | h
    · have hz : cliqueVec m l i = (0, 0) := by
        simp only [cliqueVec]
        rw [ite_eq_left (by omega)]
      rw [hz]; simp
    · have h1 : cliqueVec m l i = (1, 0) := by
        simp only [cliqueVec]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      have h2 : cliqueVec m k i = (1, 0) := by
        simp only [cliqueVec]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      rw [h1, h2]; simp
  · intro h; simp at h

theorem cliqueVec_ne (m k l : ℕ) (h : k ≠ l) (hk : k ≤ 2 * m) (hl : l ≤ 2 * m) :
    hypForm 2 m (cliqueVec m k) (cliqueVec m l) = 1 := by
  rcases lt_or_gt_of_ne h with h' | h'
  · exact cliqueVec_pair m k l h' hl
  · rw [hypForm_swap, cliqueVec_pair m l k h' hk]
    decide

/-- **Lemma 4.6**, first half: an extraspecial `2`-group of order `2^{1+2m}` has
`ω(E) = 2m + 1`. -/
theorem extraspecial_omega {m : ℕ} {E : Type} [Group E]
    (D : ExtraspecialData m E) : omegaG E = ((2 * m + 1 : ℕ) : ℕ∞) := by
  apply le_antisymm
  · rw [omegaG_le_iff]
    intro S hS
    have hinj : Set.InjOn D.pi (S : Set E) := by
      intro x hx y hy hxy
      by_contra hne
      refine hS hx hy hne ?_
      rw [← commutatorElement_eq_one_iff_commute, D.comm_iff, hxy]
      exact hypForm_isAlt 2 m _
    have hnonorth : IsNonorthSet (hypForm 2 m) ((S.image D.pi : Finset _) : Set _) := by
      intro u hu w hw huw
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hu hw
      obtain ⟨x, hx, rfl⟩ := hu
      obtain ⟨y, hy, rfl⟩ := hw
      have hne : x ≠ y := fun h => huw (by rw [h])
      intro hzero
      exact hS hx hy hne (commutatorElement_eq_one_iff_commute.mp ((D.comm_iff x y).mpr hzero))
    have hb := card_nonorth_le_finrank_succ (hypForm 2 m) (hypForm_isAlt 2 m) _ hnonorth
    rwa [Finset.card_image_of_injOn hinj, finrank_hyp_space] at hb
  · choose e he using D.pi_surj
    set S : Finset E := (Finset.range (2 * m + 1)).image (fun k => e (cliqueVec m k)) with hSdef
    have hkey : ∀ k ∈ Finset.range (2 * m + 1), ∀ l ∈ Finset.range (2 * m + 1), k ≠ l →
        ¬ Commute (e (cliqueVec m k)) (e (cliqueVec m l)) := by
      intro k hk l hl hkl
      simp only [Finset.mem_range] at hk hl
      rw [← commutatorElement_eq_one_iff_commute, D.comm_iff, he, he,
        cliqueVec_ne m k l hkl (by omega) (by omega)]
      decide
    have hinj : Set.InjOn (fun k => e (cliqueVec m k)) (Finset.range (2 * m + 1) : Set ℕ) := by
      intro k hk l hl hkl
      by_contra hne
      exact hkey k hk l hl hne (by rw [show e (cliqueVec m k) = e (cliqueVec m l) from hkl])
    have hS : IsNoncommSet (S : Set E) := by
      intro x hx y hy hxy
      rw [hSdef] at hx hy
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
      obtain ⟨k, hk, rfl⟩ := hx
      obtain ⟨l, hl, rfl⟩ := hy
      exact hkey k hk l hl (fun h => hxy (by rw [h]))
    have hcard := card_le_omegaG S hS
    rwa [hSdef, Finset.card_image_of_injOn hinj, Finset.card_range] at hcard

/-- The lower bound half of the second part of **Lemma 4.6**: `a(E) ≥ 2^m + 1`.  The image of an
abelian subgroup in the central quotient is an isotropic subspace, hence has at most `2^m`
elements, and covering the `2^{2m}` points of the quotient by such subspaces needs at least
`(2^{2m} - 1)/(2^m - 1) = 2^m + 1` of them. -/
theorem extraspecial_a_lower {m : ℕ} (hm : 1 ≤ m) {E : Type} [Group E]
    (D : ExtraspecialData m E) : ((2 ^ m + 1 : ℕ) : ℕ∞) ≤ aG E := by
  refine le_iInf ?_
  rintro ⟨C, hC⟩
  have hpi1 : D.pi 1 = 0 := by
    have h := (D.pi_mul 1 1).symm
    simp only [mul_one] at h
    simpa using h
  have hz2 : ∀ d : ZMod 2, d = 0 ∨ d = 1 := by decide
  have hsub : ∀ A : Subgroup E, ∃ W : Submodule (ZMod 2) (Fin m → ZMod 2 × ZMod 2),
      ∀ v, (v ∈ W ↔ ∃ x ∈ A, D.pi x = v) := by
    intro A
    refine ⟨{ carrier := {v | ∃ x ∈ A, D.pi x = v}
              add_mem' := ?_
              zero_mem' := ⟨1, A.one_mem, hpi1⟩
              smul_mem' := ?_ }, fun v => Iff.rfl⟩
    · rintro a b ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      exact ⟨x * y, A.mul_mem hx hy, D.pi_mul x y⟩
    · rintro c a ⟨x, hx, rfl⟩
      rcases hz2 c with rfl | rfl
      · exact ⟨1, A.one_mem, by simp [hpi1]⟩
      · exact ⟨x, hx, by simp⟩
  choose W hW using hsub
  have hcardW : ∀ A ∈ C, Nat.card (W A) ≤ 2 ^ m := by
    intro A hA
    refine isotropic_card_le m (W A) ?_
    intro u hu v hv
    obtain ⟨x, hx, rfl⟩ := (hW A u).mp hu
    obtain ⟨y, hy, rfl⟩ := (hW A v).mp hv
    exact (D.comm_iff x y).mp (commutatorElement_eq_one_iff_commute.mpr (hC.1 A hA x hx y hy))
  set T : Subgroup E → Finset (Fin m → ZMod 2 × ZMod 2) :=
    fun A => (W A : Set (Fin m → ZMod 2 × ZMod 2)).toFinset with hT
  have hTcard : ∀ A ∈ C, (T A).card ≤ 2 ^ m := by
    intro A hA
    have h1 : (T A).card = Nat.card (W A) := by
      rw [hT, Set.toFinset_card, Nat.card_eq_fintype_card]
      exact Fintype.card_congr (Equiv.refl _)
    rw [h1]
    exact hcardW A hA
  have hTzero : ∀ A, (0 : Fin m → ZMod 2 × ZMod 2) ∈ T A := by
    intro A; rw [hT]; simp only [Set.mem_toFinset]; exact (W A).zero_mem
  have hcover : (Finset.univ.erase (0 : Fin m → ZMod 2 × ZMod 2)) ⊆
      C.biUnion (fun A => (T A).erase 0) := by
    intro v hv
    obtain ⟨x, hx⟩ := D.pi_surj v
    obtain ⟨A, hA, hxA⟩ := hC.2 x
    refine Finset.mem_biUnion.mpr ⟨A, hA, Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hv, ?_⟩⟩
    rw [hT]
    simp only [Set.mem_toFinset, SetLike.mem_coe]
    exact (hW A v).mpr ⟨x, hxA, hx⟩
  have hbig : (4 : ℕ) ^ m - 1 ≤ C.card * (2 ^ m - 1) := by
    have h1 : (Finset.univ.erase (0 : Fin m → ZMod 2 × ZMod 2)).card = 4 ^ m - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      simp
    have h2 := Finset.card_le_card hcover
    have h3 := Finset.card_biUnion_le (s := C) (t := fun A => (T A).erase 0)
    have h4 : ∑ A ∈ C, ((T A).erase 0).card ≤ ∑ _A ∈ C, (2 ^ m - 1) := by
      refine Finset.sum_le_sum ?_
      intro A hA
      rw [Finset.card_erase_of_mem (hTzero A)]
      exact Nat.sub_le_sub_right (hTcard A hA) 1
    rw [Finset.sum_const, smul_eq_mul] at h4
    omega
  have ht : (2 : ℕ) ≤ 2 ^ m := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hkey : ∀ t : ℕ, 1 ≤ t → t * t - 1 = (t + 1) * (t - 1) := by
    intro t htt
    obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have h : (u + 1) * (u + 1) = (u + 1 + 1) * u + 1 := by ring
    omega
  have hfact : (4 : ℕ) ^ m - 1 = (2 ^ m + 1) * (2 ^ m - 1) := by
    rw [show (4 : ℕ) ^ m = 2 ^ m * 2 ^ m by rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]]
    exact hkey (2 ^ m) (by omega)
  rw [hfact] at hbig
  exact_mod_cast Nat.le_of_mul_le_mul_right hbig (by omega)

/-- **Lemma 4.6**, second half: an extraspecial `2`-group of order `2^{1+2m}` has
`a(E) = 2^m + 1`. -/
theorem extraspecial_a {m : ℕ} (hm : 1 ≤ m) {E : Type} [Group E] [Finite E]
    (D : ExtraspecialData m E) : aG E = ((2 ^ m + 1 : ℕ) : ℕ∞) := by
  classical
  refine le_antisymm ?_ (extraspecial_a_lower hm D)
  have hpi1 : D.pi 1 = 0 := by
    have h := (D.pi_mul 1 1).symm
    simp only [mul_one] at h
    simpa using h
  have hpiinv : ∀ x : E, D.pi x⁻¹ = - D.pi x := by
    intro x
    have h := D.pi_mul x x⁻¹
    rw [mul_inv_cancel, hpi1] at h
    linear_combination -h
  -- the preimage of an isotropic subspace is an abelian subgroup
  set sub : Submodule (ZMod 2) (Fin m → ZMod 2 × ZMod 2) → Subgroup E := fun W =>
    { carrier := {x : E | D.pi x ∈ W}
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq, D.pi_mul] at *
        exact W.add_mem hx hy
      one_mem' := by
        simp only [Set.mem_ofPred_eq, hpi1]
        exact W.zero_mem
      inv_mem' := by
        intro x hx
        simp only [Set.mem_ofPred_eq, hpiinv] at *
        exact W.neg_mem hx } with hsub
  have hmemsub : ∀ W x, x ∈ sub W ↔ D.pi x ∈ W := fun W x => Iff.rfl
  obtain ⟨F, hcard, hiso, hcover⟩ := hyp_spread 2 m
  refine le_trans (aG_le_of_cover (F.image sub) ⟨?_, ?_⟩) ?_
  · intro A hA x hx y hy
    obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hA
    rw [← commutatorElement_eq_one_iff_commute, D.comm_iff]
    exact hiso W hW (D.pi x) ((hmemsub W x).mp hx) (D.pi y) ((hmemsub W y).mp hy)
  · intro g
    obtain ⟨W, hW, hg⟩ := hcover (D.pi g)
    exact ⟨sub W, Finset.mem_image_of_mem _ hW, (hmemsub W g).mpr hg⟩
  · have h1 : (F.image sub).card ≤ 2 ^ m + 1 := le_trans Finset.card_image_le hcard
    exact_mod_cast h1

/-- **Lemma 4.6** (Extraspecial lower bound): for an extraspecial `2`-group of order `2^{1+2m}`,
`ω(E) = 2m + 1` and `a(E) = 2^m + 1`. -/
theorem extraspecial_params {m : ℕ} (hm : 1 ≤ m) {E : Type} [Group E] [Finite E]
    (D : ExtraspecialData m E) :
    omegaG E = ((2 * m + 1 : ℕ) : ℕ∞) ∧ aG E = ((2 ^ m + 1 : ℕ) : ℕ∞) :=
  ⟨extraspecial_omega D, extraspecial_a hm D⟩

/-- **Lemma 4.6**, first consequence: the extraspecial groups force `h(n) ≥ 2^m + 1`. -/
theorem hFun_ge_extraspecial (hE : ExtraspecialExists) (m n : ℕ) (hm : 1 ≤ m)
    (hmn : 2 * m + 1 ≤ n) : ((2 ^ m + 1 : ℕ) : ℕ∞) ≤ hFun n := by
  obtain ⟨E, inst, hfin, ⟨D⟩⟩ := hE m
  have homega := @extraspecial_omega m E inst D
  have hlow := @extraspecial_a_lower m hm E inst D
  refine le_trans hlow (le_sSup ⟨E, inst, ?_, rfl⟩)
  rw [homega]
  exact_mod_cast hmn

/-- **Lemma 4.6**, consequence: `log₂ h(n) ≥ n/2 - O(1)` whenever `h(n)` is finite (which the
upper bound of Theorem 2.2 guarantees). -/
theorem log2h_nonneg (n : ℕ) : 0 ≤ log2h n := by
  unfold log2h
  rcases Nat.eq_zero_or_pos ((hFun n).toNat) with h | h
  · rw [h]; simp
  · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast h)

theorem log2h_lower (hE : ExtraspecialExists) :
    ∃ C : ℝ, ∀ n : ℕ, hFun n ≠ ⊤ → (n : ℝ) / 2 - C ≤ log2h n := by
  refine ⟨2, ?_⟩
  intro n hfin
  rcases le_or_gt n 4 with h | h
  · have hn : (n : ℝ) ≤ 4 := by exact_mod_cast h
    linarith [log2h_nonneg n]
  · set m := (n - 1) / 2 with hmdef
    have hm1 : 1 ≤ m := by omega
    have hmn : 2 * m + 1 ≤ n := by omega
    have hge := hFun_ge_extraspecial hE m n hm1 hmn
    have htoNat : 2 ^ m + 1 ≤ (hFun n).toNat := by
      have := ENat.toNat_le_toNat hge hfin
      simpa only [ENat.toNat_natCast] using this
    have h2m : ((2 : ℝ) ^ m) ≤ ((hFun n).toNat : ℝ) := by
      have h' : ((2 ^ m : ℕ) : ℝ) ≤ ((hFun n).toNat : ℝ) := by
        exact_mod_cast Nat.le_of_lt (by omega)
      simpa using h'
    have hlog : (m : ℝ) ≤ log2h n := by
      unfold log2h
      have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (x := (2 : ℝ) ^ m) (by positivity) h2m
      simpa [Real.logb_pow, Real.logb_self_eq_one] using this
    have hmR : ((n : ℝ) - 2) / 2 ≤ (m : ℝ) := by
      have hnm : n - 2 ≤ 2 * m := by omega
      have hn2 : (2 : ℕ) ≤ n := by omega
      have h2 : ((n : ℝ) - 2) ≤ 2 * (m : ℝ) := by
        have := (Nat.cast_le (α := ℝ)).mpr hnm
        push_cast [Nat.cast_sub hn2] at this
        linarith
      linarith
    linarith

/-! ## 5. Central-factor descent in a finite `p`-group -/

/-- `log₂ a(G)`. -/
noncomputable def log2a (G : Type) [Group G] : ℝ := Real.logb 2 ((aG G).toNat)

/-- A central series `1 = K₀ < K₁ < ⋯ < K_L = P'` of the derived subgroup with factors of order
`p` that are central in the corresponding quotient (Lemma 5.1). -/
structure CentralFactorSeries (p : ℕ) (P : Type) [Group P] : Type where
  /-- The length of the series. -/
  L : ℕ
  /-- The terms of the series. -/
  K : ℕ → Subgroup P
  /-- The series starts at the trivial subgroup. -/
  K_zero : K 0 = ⊥
  /-- The series ends at the derived subgroup. -/
  K_top : K L = commutator P
  /-- The series is increasing. -/
  K_le : ∀ i, K i ≤ K (i + 1)
  /-- Each factor has order `p`. -/
  K_card : ∀ i < L, Nat.card (K (i + 1)) = p * Nat.card (K i)
  /-- Each term is normal. -/
  K_normal : ∀ i, (K i).Normal
  /-- Each factor is central in the corresponding quotient. -/
  K_central : ∀ i < L, ∀ x ∈ K (i + 1), ∀ g : P, ⁅x, g⁆ ∈ K i

/-- In a finite nilpotent group every nontrivial normal subgroup meets the centre. -/
theorem nilpotent_exists_center_mem_of_normal {Q : Type} [Group Q] [Finite Q]
    [Group.IsNilpotent Q]
    (M : Subgroup Q) [M.Normal] (hM : M ≠ ⊥) :
    ∃ x ∈ M, x ≠ 1 ∧ x ∈ Subgroup.center Q := by
  classical
  have hex : ∃ i, M ⊓ Subgroup.upperCentralSeries Q i ≠ ⊥ := by
    refine ⟨Group.nilpotencyClass Q, ?_⟩
    rw [Subgroup.upperCentralSeries_nilpotencyClass, inf_top_eq]
    exact hM
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := by
    refine ⟨Nat.find hex - 1, ?_⟩
    have h0 : Nat.find hex ≠ 0 := by
      intro h
      have := Nat.find_spec hex
      rw [h, Subgroup.upperCentralSeries_zero, inf_bot_eq] at this
      exact this rfl
    omega
  have hspec := Nat.find_spec hex
  rw [hj] at hspec
  have hmin : M ⊓ Subgroup.upperCentralSeries Q j = ⊥ := by
    by_contra h
    have := Nat.find_min' hex (m := j) h
    omega
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hspec
  obtain ⟨hxM, hxZ⟩ := x.2
  refine ⟨(x : Q), hxM, fun h => hx1 (Subtype.ext h), ?_⟩
  rw [Subgroup.mem_center_iff]
  intro g
  have hcomm : (x : Q) * g * (x : Q)⁻¹ * g⁻¹ ∈
      M ⊓ Subgroup.upperCentralSeries Q j := by
    constructor
    · have h1 : g * (x : Q)⁻¹ * g⁻¹ ∈ M := Subgroup.Normal.conj_mem ‹M.Normal› _ (M.inv_mem hxM) g
      have : (x : Q) * g * (x : Q)⁻¹ * g⁻¹ = (x : Q) * (g * (x : Q)⁻¹ * g⁻¹) := by group
      rw [this]
      exact M.mul_mem hxM h1
    · exact (Subgroup.mem_upperCentralSeries_succ_iff.mp hxZ) g
  rw [hmin] at hcomm
  have h3 : ⁅(x : Q), g⁆ = 1 := Subgroup.mem_bot.mp hcomm
  exact ((commutatorElement_eq_one_iff_commute.mp h3).symm).eq

/-- One step of the central-factor series: a normal subgroup properly inside the derived
subgroup can be enlarged by a central factor of order `q`. -/
theorem pgroup_central_step {q : ℕ} [Fact q.Prime] {P : Type} [Group P] [Finite P]
    (hP : IsPGroup q P)
    (N : Subgroup P) [hN : N.Normal] (hNle : N ≤ commutator P) (hne : N ≠ commutator P) :
    ∃ N' : Subgroup P, N'.Normal ∧ N ≤ N' ∧ N' ≤ commutator P ∧
      Nat.card N' = q * Nat.card N ∧ ∀ x ∈ N', ∀ g : P, ⁅x, g⁆ ∈ N := by
  classical
  have hQp : IsPGroup q (P ⧸ N) := hP.to_quotient N
  have : Group.IsNilpotent (P ⧸ N) := hQp.isNilpotent
  set f : P →* P ⧸ N := QuotientGroup.mk' N with hf
  have hfsurj : Function.Surjective f := QuotientGroup.mk'_surjective N
  set M : Subgroup (P ⧸ N) := Subgroup.map f (commutator P) with hM
  have : M.Normal := Subgroup.Normal.map inferInstance f hfsurj
  have hMne : M ≠ ⊥ := by
    intro h
    apply hne
    refine le_antisymm hNle ?_
    intro c hc
    have hc1 : f c = 1 := by
      rw [← Subgroup.mem_bot, ← h]
      exact Subgroup.mem_map_of_mem f hc
    exact (QuotientGroup.eq_one_iff c).mp hc1
  obtain ⟨x, hxM, hx1, hxZ⟩ := nilpotent_exists_center_mem_of_normal M hMne
  have hSnt : Nontrivial (M ⊓ Subgroup.center (P ⧸ N) : Subgroup (P ⧸ N)) :=
    ⟨⟨⟨x, hxM, hxZ⟩, 1, fun h => hx1 (congrArg Subtype.val h)⟩⟩
  have hSp : IsPGroup q (M ⊓ Subgroup.center (P ⧸ N) : Subgroup (P ⧸ N)) :=
    hQp.to_subgroup _
  obtain ⟨n, hn0, hcard⟩ := (hSp.nontrivial_iff_card).mp hSnt
  have : Fintype (M ⊓ Subgroup.center (P ⧸ N) : Subgroup (P ⧸ N)) := Fintype.ofFinite _
  have hdvd : q ∣ Fintype.card (M ⊓ Subgroup.center (P ⧸ N) : Subgroup (P ⧸ N)) := by
    rw [← Nat.card_eq_fintype_card, hcard]
    exact dvd_pow_self q (by omega)
  obtain ⟨z0, hz0⟩ := exists_prime_orderOf_dvd_card q hdvd
  have hzorder : orderOf (z0 : P ⧸ N) = q := by
    rw [Subgroup.orderOf_coe]; exact hz0
  have hzM : (z0 : P ⧸ N) ∈ M := z0.2.1
  have hzZ : (z0 : P ⧸ N) ∈ Subgroup.center (P ⧸ N) := z0.2.2
  set Z : Subgroup (P ⧸ N) := Subgroup.zpowers (z0 : P ⧸ N) with hZ
  have hZcenter : Z ≤ Subgroup.center (P ⧸ N) := by
    rw [hZ, Subgroup.zpowers_le]
    exact hzZ
  have hZnormal : Z.Normal := by
    constructor
    intro y hy g
    have : g * y = y * g := Subgroup.mem_center_iff.mp (hZcenter hy) g
    rw [this, mul_assoc, mul_inv_cancel, mul_one]
    exact hy
  refine ⟨Subgroup.comap f Z, inferInstance, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have : f y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
    rw [Subgroup.mem_comap, this]
    exact Z.one_mem
  · have hZM : Z ≤ M := by
      rw [hZ, Subgroup.zpowers_le]
      exact hzM
    have h1 : Subgroup.comap f Z ≤ Subgroup.comap f M := Subgroup.comap_mono hZM
    have h2 : Subgroup.comap f M = commutator P := by
      rw [hM, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hNle]
    rwa [h2] at h1
  · have h1 : Nat.card (Subgroup.comap f Z) * (Subgroup.comap f Z).index = Nat.card P :=
      Subgroup.card_mul_index _
    have h2 : Nat.card N * N.index = Nat.card P := Subgroup.card_mul_index _
    have h3 : (Subgroup.comap f Z).index = Z.index := Subgroup.index_comap_of_surjective Z hfsurj
    have h4 : Nat.card Z * Z.index = Nat.card (P ⧸ N) := Subgroup.card_mul_index Z
    have h5 : Nat.card Z = q := by rw [hZ, Nat.card_zpowers, hzorder]
    have h6 : N.index = Nat.card (P ⧸ N) := rfl
    have hZipos : 0 < Z.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have hkey : Nat.card (Subgroup.comap f Z) * Z.index = (q * Nat.card N) * Z.index :=
      calc Nat.card (Subgroup.comap f Z) * Z.index
          = Nat.card (Subgroup.comap f Z) * (Subgroup.comap f Z).index := by rw [h3]
        _ = Nat.card P := h1
        _ = Nat.card N * N.index := h2.symm
        _ = Nat.card N * (Nat.card Z * Z.index) := by rw [h6, h4]
        _ = q * Nat.card N * Z.index := by rw [h5]; ring
    exact Nat.eq_of_mul_eq_mul_right hZipos hkey
  · intro y hy g
    have hy' : f y ∈ Z := hy
    have hcent : f y ∈ Subgroup.center (P ⧸ N) := hZcenter hy'
    have : f ⁅y, g⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact (Subgroup.mem_center_iff.mp hcent (f g)).symm
    exact (QuotientGroup.eq_one_iff _).mp this

theorem centralFactorSeries_aux {q : ℕ} [Fact q.Prime] {P : Type} [Group P] [Finite P]
    (hP : IsPGroup q P) :
    ∀ (n : ℕ) (N : Subgroup P), N.Normal → N ≤ commutator P →
      Nat.card (commutator P) ≤ Nat.card N * q ^ n →
      ∃ (L : ℕ) (K : ℕ → Subgroup P), K 0 = N ∧ K L = commutator P ∧
        (∀ i, K i ≤ K (i + 1)) ∧ (∀ i < L, Nat.card (K (i + 1)) = q * Nat.card (K i)) ∧
        (∀ i, (K i).Normal) ∧ (∀ i < L, ∀ x ∈ K (i + 1), ∀ g : P, ⁅x, g⁆ ∈ K i) := by
  intro n
  induction n with
  | zero =>
    intro N hNn hNle hcard
    have := hNn
    have heq : N = commutator P :=
      Subgroup.eq_of_le_of_card_ge hNle (by simpa using hcard)
    exact ⟨0, fun _ => N, rfl, heq, fun _ => le_rfl, by omega, fun _ => hNn, by omega⟩
  | succ n ih =>
    intro N hNn hNle hcard
    have := hNn
    by_cases heq : N = commutator P
    · exact ⟨0, fun _ => N, rfl, heq, fun _ => le_rfl, by omega, fun _ => hNn, by omega⟩
    · obtain ⟨N', hN'n, hNN', hN'le, hN'card, hN'cent⟩ := pgroup_central_step hP N hNle heq
      have hcard' : Nat.card (commutator P) ≤ Nat.card N' * q ^ n := by
        rw [hN'card]
        calc Nat.card (commutator P) ≤ Nat.card N * q ^ (n + 1) := hcard
          _ = q * Nat.card N * q ^ n := by ring
      obtain ⟨L, K, hK0, hKL, hKle, hKcard, hKnorm, hKcent⟩ := ih N' hN'n hN'le hcard'
      refine ⟨L + 1, fun i => match i with | 0 => N | j + 1 => K j, rfl, hKL, ?_, ?_, ?_, ?_⟩
      · intro i
        cases i with
        | zero => simpa [hK0] using hNN'
        | succ j => exact hKle j
      · intro i hi
        cases i with
        | zero => simpa [hK0] using hN'card
        | succ j => exact hKcard j (by omega)
      · intro i
        cases i with
        | zero => exact hNn
        | succ j => exact hKnorm j
      · intro i hi
        cases i with
        | zero =>
          intro x hx g
          exact hN'cent x (hK0 ▸ (hx : x ∈ K 0)) g
        | succ j => exact hKcent j (by omega)


theorem exists_centralFactorSeries_data {q : ℕ} [Fact q.Prime] {P : Type} [Group P]
    [Finite P] (hP : IsPGroup q P) :
    ∃ (L : ℕ) (K : ℕ → Subgroup P), K 0 = ⊥ ∧ K L = commutator P ∧
        (∀ i, K i ≤ K (i + 1)) ∧ (∀ i < L, Nat.card (K (i + 1)) = q * Nat.card (K i)) ∧
        (∀ i, (K i).Normal) ∧ (∀ i < L, ∀ x ∈ K (i + 1), ∀ g : P, ⁅x, g⁆ ∈ K i) := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (hP.to_subgroup (commutator P))
  refine centralFactorSeries_aux hP n ⊥ inferInstance bot_le ?_
  rw [hn, Subgroup.card_bot, one_mul]

/-- **Lemma 5.1** (Central-factor series). -/
theorem exists_centralFactorSeries (q : ℕ) [Fact q.Prime] (P : Type) [Group P] [Finite P]
    (hP : IsPGroup q P) : Nonempty (CentralFactorSeries q P) := by
  obtain ⟨L, K, hK0, hKL, hKle, hKcard, hKnorm, hKcent⟩ := exists_centralFactorSeries_data hP
  exact ⟨⟨L, K, hK0, hKL, hKle, hKcard, hKnorm, hKcent⟩⟩

/-- A central factor of order `q` carries a `ZMod q`-valued character with kernel the smaller
term. -/
theorem exists_factor_char {q : ℕ} [Fact q.Prime] {P : Type} [Group P] [Finite P]
    (M M' : Subgroup P) [M'.Normal] (hle : M' ≤ M)
    (hcard : Nat.card M = q * Nat.card M') :
    ∃ chi : P → ZMod q, (∀ x ∈ M, ∀ y ∈ M, chi (x * y) = chi x + chi y) ∧
      (∀ x ∈ M, (chi x = 0 ↔ x ∈ M')) := by
  classical
  set N : Subgroup M := M'.subgroupOf M with hN
  have : N.Normal := Subgroup.Normal.subgroupOf ‹M'.Normal› M
  have hNcard : Nat.card N = Nat.card M' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hidx : N.index = q := by
    have h1 : Nat.card N * N.index = Nat.card M := Subgroup.card_mul_index N
    rw [hNcard, hcard] at h1
    have hpos : 0 < Nat.card M' := Nat.card_pos
    have : Nat.card M' * N.index = Nat.card M' * q := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hq1 : Nat.card (M ⧸ N) = q := hidx
  have hq2 : Nat.card (Multiplicative (ZMod q)) = q := by
    simp [Nat.card_eq_fintype_card, ZMod.card]
  set e : (M ⧸ N) ≃* Multiplicative (ZMod q) := mulEquivOfPrimeCardEq hq1 hq2 with he
  refine ⟨fun x => if h : x ∈ M then Multiplicative.toAdd (e (QuotientGroup.mk ⟨x, h⟩)) else 0,
    ?_, ?_⟩
  · intro x hx y hy
    have hxy : x * y ∈ M := M.mul_mem hx hy
    simp only [dite_eq_left hx, dite_eq_left hy, dite_eq_left hxy]
    have : (QuotientGroup.mk ⟨x * y, hxy⟩ : M ⧸ N)
        = QuotientGroup.mk ⟨x, hx⟩ * QuotientGroup.mk ⟨y, hy⟩ := rfl
    rw [this, map_mul]
    rfl
  · intro x hx
    simp only [dite_eq_left hx]
    constructor
    · intro h0
      have h1 : e (QuotientGroup.mk ⟨x, hx⟩) = 1 := by simpa using h0
      have h2 : (QuotientGroup.mk ⟨x, hx⟩ : M ⧸ N) = 1 := by
        have := congrArg e.symm h1
        simpa using this
      exact (QuotientGroup.eq_one_iff (⟨x, hx⟩ : M)).mp h2
    · intro hxM'
      have h3 : (⟨x, hx⟩ : M) ∈ N := hxM'
      have h2 : (QuotientGroup.mk ⟨x, hx⟩ : M ⧸ N) = 1 := (QuotientGroup.eq_one_iff _).mpr h3
      rw [h2, map_one]
      rfl

/-- The core of Lemma 5.2, stated for an abstract central factor `M' ≤ M` of order `q`. -/
theorem descent_core {q : ℕ} [Fact q.Prime] {P : Type} [Group P] [Finite P]
    (M M' : Subgroup P) [M'.Normal] (hle : M' ≤ M)
    (hcard : Nat.card M = q * Nat.card M')
    (hcent : ∀ x ∈ M, ∀ g : P, ⁅x, g⁆ ∈ M')
    (A : Subgroup P) (hA : ⁅A, A⁆ ≤ M) :
    ∃ (r : ℕ) (f : AltForm q (Fin r → ZMod q)) (pr : P → (Fin r → ZMod q)),
      (∀ x ∈ A, ∀ y ∈ A, pr (x * y) = pr x + pr y) ∧
      (∀ v, ∃ x ∈ A, pr x = v) ∧ IsAltForm f ∧ formRadical f = ⊥ ∧
      (∀ x ∈ A, ∀ y ∈ A, (f (pr x) (pr y) = 0 ↔ ⁅x, y⁆ ∈ M')) ∧
      ∃ cover : Finset (Subgroup P), cover.card ≤ q ^ (r / 2) + 1 ∧
        (∀ A' ∈ cover, A' ≤ A ∧ ⁅A', A'⁆ ≤ M') ∧
        ∀ x ∈ A, ∃ A' ∈ cover, x ∈ A' := by
  classical
  obtain ⟨chi, hmul, hker⟩ := exists_factor_char M M' hle hcard
  -- basic properties of the character
  have hone : chi 1 = 0 := by
    have := hmul 1 M.one_mem 1 M.one_mem
    simp only [mul_one] at this
    linear_combination -this
  have hzero : ∀ u ∈ M', chi u = 0 := fun u hu => (hker u (hle hu)).mpr hu
  have hinv : ∀ u ∈ M, chi u⁻¹ = - chi u := by
    intro u hu
    have := hmul u hu u⁻¹ (M.inv_mem hu)
    rw [mul_inv_cancel, hone] at this
    linear_combination -this
  -- commutators of elements of `A` lie in `M`
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, ⁅x, y⁆ ∈ M := fun x hx y hy =>
    hA (Subgroup.commutator_mem_commutator hx hy)
  -- conjugation does not change the character
  have hconj : ∀ u ∈ M, ∀ g : P, chi (g * u * g⁻¹) = chi u := by
    intro u hu g
    have hc : ⁅g, u⁆ ∈ M' := by
      have : ⁅u, g⁆ ∈ M' := hcent u hu g
      have h2 : ⁅g, u⁆ = ⁅u, g⁆⁻¹ := by group
      rw [h2]; exact M'.inv_mem this
    have heq : g * u * g⁻¹ = ⁅g, u⁆ * u := by group
    rw [heq, hmul _ (hle hc) _ hu, hzero _ hc, zero_add]
  -- the pairing
  set bil : P → P → ZMod q := fun x y => chi ⁅x, y⁆ with hbil
  have hbil_skew : ∀ x ∈ A, ∀ y ∈ A, bil x y = - bil y x := by
    intro x hx y hy
    have h1 : ⁅x, y⁆ = ⁅y, x⁆⁻¹ := by group
    simp only [hbil, h1]
    exact hinv _ (hcomm y hy x hx)
  have hbil_left : ∀ x ∈ A, ∀ z ∈ A, ∀ y ∈ A, bil (x * z) y = bil x y + bil z y := by
    intro x hx z hz y hy
    have heq : ⁅x * z, y⁆ = (x * ⁅z, y⁆ * x⁻¹) * ⁅x, y⁆ := by group
    have h1 : x * ⁅z, y⁆ * x⁻¹ ∈ M := by
      have := hcomm z hz y hy
      have hn : ⁅x, ⁅z, y⁆⁆ ∈ M' := by
        have h2 : ⁅⁅z, y⁆, x⁆ ∈ M' := hcent _ this x
        have h3 : ⁅x, ⁅z, y⁆⁆ = ⁅⁅z, y⁆, x⁆⁻¹ := by group
        rw [h3]; exact M'.inv_mem h2
      have heq2 : x * ⁅z, y⁆ * x⁻¹ = ⁅x, ⁅z, y⁆⁆ * ⁅z, y⁆ := by group
      rw [heq2]
      exact M.mul_mem (hle hn) this
    simp only [hbil, heq]
    rw [hmul _ h1 _ (hcomm x hx y hy), hconj _ (hcomm z hz y hy) x]
    ring
  have hbil_right : ∀ x ∈ A, ∀ y ∈ A, ∀ w ∈ A, bil x (y * w) = bil x y + bil x w := by
    intro x hx y hy w hw
    have h1 := hbil_skew x hx (y * w) (A.mul_mem hy hw)
    have h2 := hbil_left y hy w hw x hx
    have h3 := hbil_skew y hy x hx
    have h4 := hbil_skew w hw x hx
    rw [h1, h2, h3, h4]
    ring
  -- the map of `A` into the dual of itself
  set Phi : A → (A → ZMod q) := fun x y => bil (x : P) (y : P) with hPhi
  have hPhi_mul : ∀ x z : A, Phi (x * z) = Phi x + Phi z := by
    intro x z
    funext y
    exact hbil_left (x : P) x.2 (z : P) z.2 (y : P) y.2
  have hPhi_one : Phi 1 = 0 := by
    funext y
    have h1 : ⁅((1 : A) : P), (y : P)⁆ = 1 := by
      simp
    simp only [hPhi, hbil, h1, hone]
    rfl
  have hPhi_pow : ∀ (n : ℕ) (x : A), ((n : ZMod q)) • Phi x = Phi (x ^ n) := by
    intro n
    induction n with
    | zero => intro x; simp [hPhi_one]
    | succ k ih =>
      intro x
      rw [pow_succ, hPhi_mul, ← ih]
      push_cast
      rw [add_smul, one_smul]
  have hmemU : ∀ a : A, Phi a ∈ Set.range Phi := fun a => ⟨a, rfl⟩
  set U : Submodule (ZMod q) (A → ZMod q) :=
    { carrier := Set.range Phi
      add_mem' := by
        rintro a b ⟨x, rfl⟩ ⟨z, rfl⟩
        exact ⟨x * z, hPhi_mul x z⟩
      zero_mem' := ⟨1, hPhi_one⟩
      smul_mem' := by
        rintro c a ⟨x, rfl⟩
        have hc : ((c.val : ℕ) : ZMod q) = c := by
          simp [ZMod.natCast_val, ZMod.cast_id]
        refine ⟨x ^ c.val, ?_⟩
        rw [← hPhi_pow, hc] } with hU
  have : Fintype (A : Type _) := Fintype.ofFinite _
  have : FiniteDimensional (ZMod q) (A → ZMod q) := by infer_instance
  set r : ℕ := Module.finrank (ZMod q) U with hr
  set E : U ≃ₗ[ZMod q] (Fin r → ZMod q) := (Module.finBasis (ZMod q) U).equivFun with hE
  set g : U → A := fun u => Classical.choose u.2 with hgdef
  have hg : ∀ u : U, Phi (g u) = (u : A → ZMod q) := fun u => Classical.choose_spec u.2
  have key : ∀ (u : U) (y y' : A), Phi y = Phi y' →
      (u : A → ZMod q) y = (u : A → ZMod q) y' := by
    rintro ⟨u, x, rfl⟩ y y' hyy'
    have h1 : bil (y : P) (x : P) = bil (y' : P) (x : P) := congrFun hyy' x
    have h2 := hbil_skew (x : P) x.2 (y : P) y.2
    have h3 := hbil_skew (x : P) x.2 (y' : P) y'.2
    show bil (x : P) (y : P) = bil (x : P) (y' : P)
    rw [h2, h3, h1]
  set F : U → U → ZMod q := fun u v => (u : A → ZMod q) (g v) with hF
  have hFbil : ∀ (x y : A), F ⟨Phi x, hmemU x⟩ ⟨Phi y, hmemU y⟩ = bil (x : P) (y : P) := by
    intro x y
    show (Phi x) (g ⟨Phi y, hmemU y⟩) = bil (x : P) (y : P)
    have := key ⟨Phi x, hmemU x⟩ (g ⟨Phi y, hmemU y⟩) y (hg ⟨Phi y, hmemU y⟩)
    exact this
  have hFskew : ∀ u v : U, F u v = - F v u := by
    rintro ⟨u, x, rfl⟩ ⟨v, y, rfl⟩
    rw [hFbil x y, hFbil y x]
    exact hbil_skew (x : P) x.2 (y : P) y.2
  have hFaddl : ∀ (u₁ u₂ v : U), F (u₁ + u₂) v = F u₁ v + F u₂ v := by
    intro u₁ u₂ v; rfl
  have hFsmull : ∀ (c : ZMod q) (u v : U), F (c • u) v = c • F u v := by
    intro c u v; rfl
  set f0 : U →ₗ[ZMod q] U →ₗ[ZMod q] ZMod q :=
    LinearMap.mk₂ (ZMod q) F hFaddl hFsmull
      (by
        intro u v₁ v₂
        rw [hFskew u (v₁ + v₂), hFaddl v₁ v₂ u, hFskew v₁ u, hFskew v₂ u]
        ring)
      (by
        intro c u v
        rw [hFskew u (c • v), hFsmull c v u, hFskew v u]
        simp) with hf0
  set fq : AltForm q (Fin r → ZMod q) :=
    f0.compl₁₂ (E.symm : (Fin r → ZMod q) →ₗ[ZMod q] U)
      (E.symm : (Fin r → ZMod q) →ₗ[ZMod q] U) with hfq
  set pr : P → (Fin r → ZMod q) :=
    fun x => if h : x ∈ A then E ⟨Phi ⟨x, h⟩, hmemU _⟩ else 0 with hprdef
  have hpr_eq : ∀ (x : P) (hx : x ∈ A), pr x = E ⟨Phi ⟨x, hx⟩, hmemU _⟩ := by
    intro x hx
    simp only [hprdef, dite_eq_left hx]
  have hpr_mul : ∀ x ∈ A, ∀ y ∈ A, pr (x * y) = pr x + pr y := by
    intro x hx y hy
    rw [hpr_eq _ (A.mul_mem hx hy), hpr_eq x hx, hpr_eq y hy, ← map_add]
    congr 1
    exact Subtype.ext (hPhi_mul ⟨x, hx⟩ ⟨y, hy⟩)
  have hpr_surj : ∀ v, ∃ x ∈ A, pr x = v := by
    intro v
    obtain ⟨x, hx⟩ := (E.symm v).2
    refine ⟨(x : P), x.2, ?_⟩
    rw [hpr_eq _ x.2]
    have : (⟨Phi ⟨(x : P), x.2⟩, hmemU _⟩ : U) = E.symm v := Subtype.ext hx
    rw [this, LinearEquiv.apply_symm_apply]
  have hfq_pr : ∀ x ∈ A, ∀ y ∈ A, fq (pr x) (pr y) = chi ⁅x, y⁆ := by
    intro x hx y hy
    rw [hpr_eq x hx, hpr_eq y hy]
    show F (E.symm (E ⟨Phi ⟨x, hx⟩, hmemU _⟩)) (E.symm (E ⟨Phi ⟨y, hy⟩, hmemU _⟩)) = _
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    exact hFbil ⟨x, hx⟩ ⟨y, hy⟩
  have hfq_alt : IsAltForm fq := by
    intro v
    obtain ⟨x, hx, rfl⟩ := hpr_surj v
    rw [hfq_pr x hx x hx]
    have : ⁅x, x⁆ = 1 := by group
    rw [this, hone]
  have hpr_one : pr 1 = 0 := by
    have := hpr_mul 1 A.one_mem 1 A.one_mem
    rw [mul_one] at this
    linear_combination (norm := module) -this
  have hpr_zero : ∀ x ∈ A, (∀ y ∈ A, chi ⁅x, y⁆ = 0) → pr x = 0 := by
    intro x hx hall
    rw [hpr_eq x hx]
    have h0 : (⟨Phi ⟨x, hx⟩, hmemU _⟩ : U) = 0 := by
      apply Subtype.ext
      funext y
      exact hall (y : P) y.2
    rw [h0, map_zero]
  have hfq_rad : formRadical fq = ⊥ := by
    rw [formRadical, Submodule.eq_bot_iff]
    intro v hv
    obtain ⟨x, hx, rfl⟩ := hpr_surj v
    refine hpr_zero x hx ?_
    intro y hy
    rw [← hfq_pr x hx y hy]
    have : fq (pr x) = 0 := hv
    rw [this]
    rfl
  have hfq_iff : ∀ x ∈ A, ∀ y ∈ A, (fq (pr x) (pr y) = 0 ↔ ⁅x, y⁆ ∈ M') := by
    intro x hx y hy
    rw [hfq_pr x hx y hy]
    exact hker _ (hcomm x hx y hy)
  -- the cover
  obtain ⟨m, prj, hsurj, hkerprj, hrank, hform⟩ := alt_normal_form fq hfq_alt
  have hreven : r = 2 * m := by
    have h1 : formRank fq = Module.finrank (ZMod q) (Fin r → ZMod q) := by
      rw [formRank, hfq_rad]
      simp
    rw [h1] at hrank
    simpa using hrank
  obtain ⟨Fs, hFcard, hFiso, hFcov⟩ := spread_cover fq hfq_alt m (by rw [hrank])
  set sub : Submodule (ZMod q) (Fin r → ZMod q) → Subgroup P := fun W =>
    { carrier := {x : P | x ∈ A ∧ pr x ∈ W}
      mul_mem' := by
        rintro x y ⟨hxA, hxW⟩ ⟨hyA, hyW⟩
        exact ⟨A.mul_mem hxA hyA, by rw [hpr_mul x hxA y hyA]; exact W.add_mem hxW hyW⟩
      one_mem' := ⟨A.one_mem, by rw [hpr_one]; exact W.zero_mem⟩
      inv_mem' := by
        rintro x ⟨hxA, hxW⟩
        refine ⟨A.inv_mem hxA, ?_⟩
        have h1 := hpr_mul x hxA x⁻¹ (A.inv_mem hxA)
        rw [mul_inv_cancel, hpr_one] at h1
        have h2 : pr x⁻¹ = - pr x := by linear_combination (norm := module) -h1
        rw [h2]
        exact W.neg_mem hxW } with hsub
  refine ⟨r, fq, pr, hpr_mul, hpr_surj, hfq_alt, hfq_rad, hfq_iff, Fs.image sub, ?_, ?_, ?_⟩
  · have h1 : (Fs.image sub).card ≤ q ^ m + 1 := le_trans Finset.card_image_le hFcard
    have h2 : r / 2 = m := by omega
    rw [h2]
    exact h1
  · intro A' hA'
    obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hA'
    refine ⟨fun x hx => hx.1, ?_⟩
    rw [Subgroup.commutator_le]
    rintro x ⟨hxA, hxW⟩ y ⟨hyA, hyW⟩
    refine (hfq_iff x hxA y hyA).mp ?_
    exact hFiso W hW (pr x) hxW (pr y) hyW
  · intro x hx
    obtain ⟨W, hW, hxW⟩ := hFcov (pr x)
    exact ⟨sub W, Finset.mem_image_of_mem _ hW, ⟨hx, hxW⟩⟩

/-- **Lemma 5.2** (Central-factor form and descent): one step of the recursion.  The subgroup `A`
with `[A, A] ≤ K_{L-j}` carries a nondegenerate alternating form on `A / R`, and `A` is covered by
at most `p^{ρ/2} + 1` subgroups whose derived subgroup lies in `K_{L-j-1}`.  (The hypothesis
that `P` is a `q`-group is part of the setting of the manuscript, but it is not needed by
the formal derivation.) -/
theorem central_factor_descent {q : ℕ} [Fact q.Prime] {P : Type} [Group P] [Finite P]
    (_hP : IsPGroup q P) (S : CentralFactorSeries q P) (j : ℕ) (hj : j < S.L) (A : Subgroup P)
    (hA : ⁅A, A⁆ ≤ S.K (S.L - j)) :
    ∃ (r : ℕ) (f : AltForm q (Fin r → ZMod q)) (pr : P → (Fin r → ZMod q)),
      (∀ x ∈ A, ∀ y ∈ A, pr (x * y) = pr x + pr y) ∧
      (∀ v, ∃ x ∈ A, pr x = v) ∧ IsAltForm f ∧ formRadical f = ⊥ ∧
      (∀ x ∈ A, ∀ y ∈ A, (f (pr x) (pr y) = 0 ↔ ⁅x, y⁆ ∈ S.K (S.L - j - 1))) ∧
      ∃ cover : Finset (Subgroup P), cover.card ≤ q ^ (r / 2) + 1 ∧
        (∀ A' ∈ cover, A' ≤ A ∧ ⁅A', A'⁆ ≤ S.K (S.L - j - 1)) ∧
        ∀ x ∈ A, ∃ A' ∈ cover, x ∈ A' := by
  have hi : S.L - j - 1 + 1 = S.L - j := by omega
  have hilt : S.L - j - 1 < S.L := by omega
  have : (S.K (S.L - j - 1)).Normal := S.K_normal _
  have hle : S.K (S.L - j - 1) ≤ S.K (S.L - j) := by
    have h := S.K_le (S.L - j - 1); rwa [hi] at h
  have hcard : Nat.card (S.K (S.L - j)) = q * Nat.card (S.K (S.L - j - 1)) := by
    have h := S.K_card _ hilt; rwa [hi] at h
  have hcent : ∀ x ∈ S.K (S.L - j), ∀ g : P, ⁅x, g⁆ ∈ S.K (S.L - j - 1) := by
    have h := S.K_central _ hilt; rwa [hi] at h
  exact descent_core _ _ hle hcard hcent A hA

/-- A root-to-leaf branch of the cover tree produced by iterating Lemma 5.2, together with the
associated scalar alternating forms. -/
structure DescentBranch (q : ℕ) [Fact q.Prime] (P : Type) [Group P]
    (S : CentralFactorSeries q P) : Type where
  /-- The chain of subgroups along the branch. -/
  A : ℕ → Subgroup P
  /-- The symplectic rank encountered at each stage. -/
  rho : ℕ → ℕ
  /-- The projection of the stage subgroup onto its symplectic quotient. -/
  pr : ∀ j : ℕ, P → (Fin (rho j) → ZMod q)
  /-- The stage form. -/
  f : ∀ j : ℕ, AltForm q (Fin (rho j) → ZMod q)
  /-- The branch starts at the whole group. -/
  A_zero : A 0 = ⊤
  /-- The branch is decreasing. -/
  A_le : ∀ j, A (j + 1) ≤ A j
  /-- Stage `j` has derived subgroup inside `K_{L-j}`. -/
  A_der : ∀ j ≤ S.L, ⁅A j, A j⁆ ≤ S.K (S.L - j)
  /-- The projection is a homomorphism on the stage subgroup. -/
  pr_mul : ∀ j, ∀ x ∈ A j, ∀ y ∈ A j, pr j (x * y) = pr j x + pr j y
  /-- The projection is onto. -/
  pr_surj : ∀ j < S.L, ∀ v, ∃ x ∈ A j, pr j x = v
  /-- The stage forms are alternating. -/
  f_alt : ∀ j, IsAltForm (f j)
  /-- The stage forms are nondegenerate. -/
  f_nondeg : ∀ j < S.L, formRadical (f j) = ⊥
  /-- The stage form computes the commutator modulo the next term of the series. -/
  f_comm : ∀ j < S.L, ∀ x ∈ A j, ∀ y ∈ A j,
    (f j (pr j x) (pr j y) = 0 ↔ ⁅x, y⁆ ∈ S.K (S.L - j - 1))
  /-- The leaf of the branch is abelian. -/
  leaf_abelian : ∀ x ∈ A S.L, ∀ y ∈ A S.L, Commute x y

/-- The interaction rank `t_{j,k}`: the dimension of the image of `A_k` in `V_j`. -/
noncomputable def interRank {q : ℕ} [Fact q.Prime] {P : Type} [Group P]
    {S : CentralFactorSeries q P} (Br : DescentBranch q P S) (j k : ℕ) : ℕ :=
  Module.finrank (ZMod q) (Submodule.span (ZMod q) (Br.pr j '' (Br.A k : Set P)))

/-- If `a(X) ≤ k` then some family of at most `k` abelian subgroups covers `X`. -/
theorem exists_cover_of_aSet_le {G : Type} [Group G] (X : Set G) (k : ℕ)
    (h : aSet X ≤ (k : ℕ∞)) :
    ∃ C : Finset (Subgroup G), (∀ A ∈ C, ∀ x ∈ A, ∀ y ∈ A, Commute x y) ∧
      (∀ g ∈ X, ∃ A ∈ C, g ∈ A) ∧ C.card ≤ k := by
  by_contra hcon
  push Not at hcon
  have hle : ((k : ℕ) + 1 : ℕ∞) ≤ aSet X := by
    refine le_iInf ?_
    rintro ⟨C, hC1, hC2⟩
    have h1 : k < C.card := hcon C hC1 hC2
    have : k + 1 ≤ C.card := by omega
    exact_mod_cast this
  have : ((k : ℕ) + 1 : ℕ∞) ≤ (k : ℕ∞) := le_trans hle h
  have h2 : ((k + 1 : ℕ) : ℕ∞) ≤ ((k : ℕ) : ℕ∞) := by exact_mod_cast this
  have := (Nat.cast_le (α := ℕ∞)).mp h2
  omega

/-- An abelian subgroup is covered by one abelian subgroup. -/
theorem aSet_le_one_of_abelian {G : Type} [Group G] (A : Subgroup G)
    (hA : ∀ x ∈ A, ∀ y ∈ A, Commute x y) : aSet (A : Set G) ≤ 1 := by
  have := iInf_le (fun C : {C : Finset (Subgroup G) //
      (∀ B ∈ C, ∀ x ∈ B, ∀ y ∈ B, Commute x y) ∧ ∀ g ∈ (A : Set G), ∃ B ∈ C, g ∈ B} =>
    ((C : Finset (Subgroup G)).card : ℕ∞))
    ⟨{A}, by
      constructor
      · intro B hB
        rw [Finset.mem_singleton] at hB
        subst hB
        exact hA
      · intro g hg
        exact ⟨A, Finset.mem_singleton_self A, hg⟩⟩
  change @LE.le ℕ∞ instCompleteLinearOrderENat.toLE (aSet (A : Set G)) 1
  unfold aSet
  exact this

/-- Covering a set by subgroups each of which has a small abelian cover. -/
theorem aSet_le_of_subgroup_cover {G : Type} [Group G] (X : Set G)
    (cover : Finset (Subgroup G)) (k : ℕ)
    (hcov : ∀ x ∈ X, ∃ A ∈ cover, x ∈ A)
    (hk : ∀ A ∈ cover, aSet (A : Set G) ≤ (k : ℕ∞)) :
    aSet X ≤ ((cover.card * k : ℕ) : ℕ∞) := by
  classical
  have hex : ∀ A ∈ cover, ∃ C : Finset (Subgroup G),
      (∀ B ∈ C, ∀ x ∈ B, ∀ y ∈ B, Commute x y) ∧
      (∀ g ∈ (A : Set G), ∃ B ∈ C, g ∈ B) ∧ C.card ≤ k :=
    fun A hA => exists_cover_of_aSet_le _ k (hk A hA)
  choose! C hC1 hC2 hC3 using hex
  set D : Finset (Subgroup G) := cover.biUnion C with hD
  have hDcard : D.card ≤ cover.card * k := by
    refine le_trans (Finset.card_biUnion_le) ?_
    calc ∑ A ∈ cover, (C A).card ≤ ∑ _A ∈ cover, k :=
          Finset.sum_le_sum (fun A hA => hC3 A hA)
      _ = cover.card * k := by rw [Finset.sum_const, smul_eq_mul]
  have hmain : aSet X ≤ (D.card : ℕ∞) := by
    refine iInf_le (fun C' : {C' : Finset (Subgroup G) //
        (∀ B ∈ C', ∀ x ∈ B, ∀ y ∈ B, Commute x y) ∧ ∀ g ∈ X, ∃ B ∈ C', g ∈ B} =>
      ((C' : Finset (Subgroup G)).card : ℕ∞)) ⟨D, ?_, ?_⟩
    · intro B hB
      obtain ⟨A, hA, hBA⟩ := Finset.mem_biUnion.mp hB
      exact hC1 A hA B hBA
    · intro g hg
      obtain ⟨A, hA, hgA⟩ := hcov g hg
      obtain ⟨B, hB, hgB⟩ := hC2 A hA g hgA
      exact ⟨B, Finset.mem_biUnion.mpr ⟨A, hA, hB⟩, hgB⟩
  exact le_trans hmain (by exact_mod_cast hDcard)

/-- Bundled data of one stage of a descent branch. -/
structure StageData (q : ℕ) [Fact q.Prime] (P : Type) [Group P] : Type where
  /-- The stage subgroup. -/
  A : Subgroup P
  /-- The symplectic rank at this stage. -/
  rho : ℕ
  /-- The projection onto the symplectic quotient. -/
  pr : P → (Fin rho → ZMod q)
  /-- The stage form. -/
  f : AltForm q (Fin rho → ZMod q)

/-- The recursive construction of a descent branch, by downward induction on the stage. -/
theorem tail_branch_exists {q : ℕ} [Fact q.Prime] {P : Type} [Group P] [Finite P]
    (hP : IsPGroup q P) (S : CentralFactorSeries q P) :
    ∀ (d j : ℕ), j + d = S.L → ∀ A : Subgroup P, ⁅A, A⁆ ≤ S.K (S.L - j) →
    ∃ D : ℕ → StageData q P, (D j).A = A ∧
      (∀ i, j ≤ i → (D (i + 1)).A ≤ (D i).A) ∧
      (∀ i, j ≤ i → i ≤ S.L → ⁅(D i).A, (D i).A⁆ ≤ S.K (S.L - i)) ∧
      (∀ i, j ≤ i → ∀ x ∈ (D i).A, ∀ y ∈ (D i).A,
        (D i).pr (x * y) = (D i).pr x + (D i).pr y) ∧
      (∀ i, j ≤ i → i < S.L → ∀ v, ∃ x ∈ (D i).A, (D i).pr x = v) ∧
      (∀ i, j ≤ i → IsAltForm (D i).f) ∧
      (∀ i, j ≤ i → i < S.L → formRadical (D i).f = ⊥) ∧
      (∀ i, j ≤ i → i < S.L → ∀ x ∈ (D i).A, ∀ y ∈ (D i).A,
        ((D i).f ((D i).pr x) ((D i).pr y) = 0 ↔ ⁅x, y⁆ ∈ S.K (S.L - i - 1))) ∧
      aSet ((D j).A : Set P)
        ≤ ((∏ i ∈ Finset.Ico j S.L, (q ^ ((D i).rho / 2) + 1) : ℕ) : ℕ∞) := by
  classical
  intro d
  induction d with
  | zero =>
    intro j hj A hA
    have hjL : j = S.L := by omega
    refine ⟨fun _ => ⟨A, 0, fun _ => 0, 0⟩, rfl, fun i _ => le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi hiL
      have hij : i = j := by omega
      subst hij
      exact hA
    · intro i _ x _ y _
      simp
    · intro i hi hiL
      exact absurd hiL (by omega)
    · intro i _ x
      rfl
    · intro i hi hiL
      exact absurd hiL (by omega)
    · intro i hi hiL
      exact absurd hiL (by omega)
    · have hIco : Finset.Ico j S.L = ∅ := by
        rw [hjL]; exact Finset.Ico_self _
      rw [hIco]
      simp only [Finset.prod_empty, Nat.cast_one]
      refine aSet_le_one_of_abelian A ?_
      intro x hx y hy
      have h1 : ⁅x, y⁆ ∈ S.K (S.L - j) := hA (Subgroup.commutator_mem_commutator hx hy)
      rw [hjL] at h1
      simp only [Nat.sub_self, S.K_zero, Subgroup.mem_bot] at h1
      exact (commutatorElement_eq_one_iff_commute.mp h1)
  | succ d ih =>
    intro j hj A hA
    have hjL : j < S.L := by omega
    obtain ⟨r, f, pr, hprmul, hprsurj, hfalt, hfrad, hfiff, cover, hcard, hcovprop, hcov⟩ :=
      central_factor_descent hP S j hjL A hA
    have hsub : S.L - j - 1 = S.L - (j + 1) := by omega
    have hchild : ∀ A' ∈ cover, ∃ D : ℕ → StageData q P, (D (j + 1)).A = A' ∧
        (∀ i, j + 1 ≤ i → (D (i + 1)).A ≤ (D i).A) ∧
        (∀ i, j + 1 ≤ i → i ≤ S.L → ⁅(D i).A, (D i).A⁆ ≤ S.K (S.L - i)) ∧
        (∀ i, j + 1 ≤ i → ∀ x ∈ (D i).A, ∀ y ∈ (D i).A,
          (D i).pr (x * y) = (D i).pr x + (D i).pr y) ∧
        (∀ i, j + 1 ≤ i → i < S.L → ∀ v, ∃ x ∈ (D i).A, (D i).pr x = v) ∧
        (∀ i, j + 1 ≤ i → IsAltForm (D i).f) ∧
        (∀ i, j + 1 ≤ i → i < S.L → formRadical (D i).f = ⊥) ∧
        (∀ i, j + 1 ≤ i → i < S.L → ∀ x ∈ (D i).A, ∀ y ∈ (D i).A,
          ((D i).f ((D i).pr x) ((D i).pr y) = 0 ↔ ⁅x, y⁆ ∈ S.K (S.L - i - 1))) ∧
        aSet ((D (j + 1)).A : Set P)
          ≤ ((∏ i ∈ Finset.Ico (j + 1) S.L, (q ^ ((D i).rho / 2) + 1) : ℕ) : ℕ∞) := by
      intro A' hA'
      refine ih (j + 1) (by omega) A' ?_
      have := (hcovprop A' hA').2
      rwa [hsub] at this
    have : Nonempty (StageData q P) := ⟨⟨⊥, 0, fun _ => 0, 0⟩⟩
    choose! Dc hDc0 hDc1 hDc2 hDc3 hDc4 hDc5 hDc6 hDc7 hDc8 using hchild
    have hne : cover.Nonempty := by
      obtain ⟨A', hA', _⟩ := hcov 1 A.one_mem
      exact ⟨A', hA'⟩
    obtain ⟨B, hB, hBmax⟩ := Finset.exists_max_image cover
      (fun A' => ∏ i ∈ Finset.Ico (j + 1) S.L, (q ^ ((Dc A' i).rho / 2) + 1)) hne
    set Dnew : ℕ → StageData q P := fun i => if i = j then ⟨A, r, pr, f⟩ else Dc B i with hDnew
    have hDj : Dnew j = ⟨A, r, pr, f⟩ := by simp [hDnew]
    have hDi : ∀ i, i ≠ j → Dnew i = Dc B i := by
      intro i hi
      simp [hDnew, hi]
    have hBA : B ≤ A := (hcovprop B hB).1
    refine ⟨Dnew, by rw [hDj], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rcases eq_or_lt_of_le hi with h | h
      · rw [← h, hDi (j + 1) (by omega), hDj, hDc0 B hB]
        exact hBA
      · rw [hDi (i + 1) (by omega), hDi i (by omega)]
        exact hDc1 B hB i (by omega)
    · intro i hi hiL
      rcases eq_or_lt_of_le hi with h | h
      · rw [← h, hDj]
        exact hA
      · rw [hDi i (by omega)]
        exact hDc2 B hB i (by omega) hiL
    · intro i hi
      rcases eq_or_lt_of_le hi with h | h
      · rw [← h, hDj]
        exact hprmul
      · rw [hDi i (by omega)]
        exact hDc3 B hB i (by omega)
    · intro i hi hiL
      rcases eq_or_lt_of_le hi with h | h
      · rw [← h, hDj]
        exact hprsurj
      · rw [hDi i (by omega)]
        exact hDc4 B hB i (by omega) hiL
    · intro i hi
      rcases eq_or_lt_of_le hi with h | h
      · rw [← h, hDj]
        exact hfalt
      · rw [hDi i (by omega)]
        exact hDc5 B hB i (by omega)
    · intro i hi hiL
      rcases eq_or_lt_of_le hi with h | h
      · rw [← h, hDj]
        exact hfrad
      · rw [hDi i (by omega)]
        exact hDc6 B hB i (by omega) hiL
    · intro i hi hiL
      rcases eq_or_lt_of_le hi with h | h
      · rw [← h, hDj]
        exact hfiff
      · rw [hDi i (by omega)]
        exact hDc7 B hB i (by omega) hiL
    · have hprod : (∏ i ∈ Finset.Ico j S.L, (q ^ ((Dnew i).rho / 2) + 1))
          = (q ^ (r / 2) + 1) * ∏ i ∈ Finset.Ico (j + 1) S.L, (q ^ ((Dc B i).rho / 2) + 1) := by
        rw [Finset.prod_eq_prod_Ico_succ_bot hjL]
        congr 1
        · rw [hDj]
        · refine Finset.prod_congr rfl ?_
          intro i hi
          rw [Finset.mem_Ico] at hi
          rw [hDi i (by omega)]
      rw [hDj, hprod]
      set Pmax := ∏ i ∈ Finset.Ico (j + 1) S.L, (q ^ ((Dc B i).rho / 2) + 1) with hPmax
      have hk : ∀ A' ∈ cover, aSet (A' : Set P) ≤ (Pmax : ℕ∞) := by
        intro A' hA'
        have h1 := hDc8 A' hA'
        rw [hDc0 A' hA'] at h1
        refine le_trans h1 ?_
        have := hBmax A' hA'
        exact_mod_cast this
      have h2 := aSet_le_of_subgroup_cover (A : Set P) cover Pmax hcov hk
      refine le_trans h2 ?_
      have h3 : cover.card * Pmax ≤ (q ^ (r / 2) + 1) * Pmax :=
        Nat.mul_le_mul_right _ hcard
      exact_mod_cast h3

theorem aG_le_aSet_top {G : Type} [Group G] : aG G ≤ aSet ((⊤ : Subgroup G) : Set G) := by
  refine le_iInf ?_
  rintro ⟨C, h1, h2⟩
  exact aG_le_of_cover C ⟨h1, fun g => h2 g (by trivial)⟩

theorem logb_two_pow_succ_le {q : ℕ} (hq : 2 ≤ q) (k : ℕ) :
    Real.logb 2 ((q : ℝ) ^ k + 1) ≤ (k : ℝ) * Real.logb 2 q + 1 := by
  have hq0 : (0 : ℝ) < q := by positivity
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.one_le_of_lt hq
  have hpow : (1 : ℝ) ≤ (q : ℝ) ^ k := one_le_pow₀ hq1
  have h1 : (q : ℝ) ^ k + 1 ≤ 2 * (q : ℝ) ^ k := by linarith
  have h2 : Real.logb 2 ((q : ℝ) ^ k + 1) ≤ Real.logb 2 (2 * (q : ℝ) ^ k) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) h1
  have h3 : Real.logb 2 (2 * (q : ℝ) ^ k) = 1 + (k : ℝ) * Real.logb 2 q := by
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num),
      Real.logb_pow]
  linarith [h2, h3.le, h3.ge]

/-- **Lemma 5.3** (Branch cover bound): the recursive cover of Lemma 5.2 is realised along some
branch, with `log₂ a(P) ≤ (log₂ p)/2 · ∑ρ_j + L`. -/
theorem branch_cover_bound {q : ℕ} [Fact q.Prime] {P : Type} [Group P] [Finite P]
    (hP : IsPGroup q P) (S : CentralFactorSeries q P) :
    ∃ Br : DescentBranch q P S,
      log2a P ≤ (Real.logb 2 q / 2) * (∑ j ∈ Finset.range S.L, (Br.rho j : ℝ)) + S.L := by
  classical
  have htop : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ ≤ S.K (S.L - 0) := by
    rw [Nat.sub_zero, S.K_top, commutator_def]
  obtain ⟨D, hD0, hD1, hD2, hD3, hD4, hD5, hD6, hD7, hD8⟩ :=
    tail_branch_exists hP S S.L 0 (by omega) ⊤ htop
  have hleaf : ∀ x ∈ (D S.L).A, ∀ y ∈ (D S.L).A, Commute x y := by
    intro x hx y hy
    have h1 : ⁅x, y⁆ ∈ S.K (S.L - S.L) :=
      hD2 S.L (Nat.zero_le _) le_rfl (Subgroup.commutator_mem_commutator hx hy)
    rw [Nat.sub_self, S.K_zero, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_commute.mp h1
  refine ⟨{ A := fun i => (D i).A
            rho := fun i => (D i).rho
            pr := fun i => (D i).pr
            f := fun i => (D i).f
            A_zero := hD0
            A_le := fun i => hD1 i (Nat.zero_le i)
            A_der := fun i hi => hD2 i (Nat.zero_le i) hi
            pr_mul := fun i => hD3 i (Nat.zero_le i)
            pr_surj := fun i hi => hD4 i (Nat.zero_le i) hi
            f_alt := fun i => hD5 i (Nat.zero_le i)
            f_nondeg := fun i hi => hD6 i (Nat.zero_le i) hi
            f_comm := fun i hi => hD7 i (Nat.zero_le i) hi
            leaf_abelian := hleaf }, ?_⟩
  -- the numerical estimate
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  set N : ℕ := ∏ i ∈ Finset.Ico 0 S.L, (q ^ ((D i).rho / 2) + 1) with hN
  have hNpos : 0 < N := by
    rw [hN]
    exact Finset.prod_pos (fun i _ => by positivity)
  have haG : aG P ≤ (N : ℕ∞) := by
    refine le_trans aG_le_aSet_top ?_
    rw [← hD0]
    exact hD8
  have htoNat : (aG P).toNat ≤ N := by
    have h1 := ENat.toNat_le_toNat haG (by simp)
    simpa using h1
  have hNpos' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNpos
  have hlog : log2a P ≤ Real.logb 2 N := by
    rw [log2a]
    rcases Nat.eq_zero_or_pos (aG P).toNat with h0 | h0
    · rw [h0]
      simpa using Real.logb_nonneg (by norm_num) hNpos'
    · refine Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast h0) ?_
      exact_mod_cast htoNat
  refine le_trans hlog ?_
  have hcast : (N : ℝ) = ∏ i ∈ Finset.range S.L, ((q : ℝ) ^ ((D i).rho / 2) + 1) := by
    rw [hN, ← Finset.range_eq_Ico]
    push_cast
    rfl
  have hprodlog : Real.logb 2 (N : ℝ)
      = ∑ i ∈ Finset.range S.L, Real.logb 2 ((q : ℝ) ^ ((D i).rho / 2) + 1) := by
    rw [hcast, Real.logb, Real.log_prod]
    · rw [Finset.sum_div]
      rfl
    · intro i _
      positivity
  rw [hprodlog]
  have hlogq : 0 ≤ Real.logb 2 q := by
    have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.one_le_of_lt hq2
    exact Real.logb_nonneg (by norm_num) this
  have hterm : ∀ i ∈ Finset.range S.L,
      Real.logb 2 ((q : ℝ) ^ ((D i).rho / 2) + 1)
        ≤ Real.logb 2 q / 2 * ((D i).rho : ℝ) + 1 := by
    intro i _
    refine le_trans (logb_two_pow_succ_le hq2 ((D i).rho / 2)) ?_
    have h1 : (((D i).rho / 2 : ℕ) : ℝ) ≤ ((D i).rho : ℝ) / 2 := by
      exact_mod_cast Nat.cast_div_le
    nlinarith [h1, hlogq]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp


/-- The span of a pairwise orthogonal set is isotropic. -/
theorem isotropic_span (φ : AltForm p V) (T : Set V) (hT : ∀ x ∈ T, ∀ y ∈ T, φ x y = 0) :
    IsIsotropic φ (Submodule.span (ZMod p) T) := by
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem a ha =>
    induction hy using Submodule.span_induction with
    | mem b hb => exact hT a ha b hb
    | zero => simp
    | add b c _ _ hb hc => simp [hb, hc]
    | smul t b _ hb => simp [hb]
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul t a _ ha => simp [ha]

/-- A nondegenerate form realises every linear functional on a linearly independent family. -/
theorem exists_dual_vector [FiniteDimensional (ZMod p) V] (φ : AltForm p V)
    (hrad : formRadical φ = ⊥) {d : ℕ} (y : Fin d → V) (hy : LinearIndependent (ZMod p) y)
    (c : Fin d → ZMod p) : ∃ v : V, ∀ h, φ v (y h) = c h := by
  classical
  set b := Module.Basis.span hy with hb
  set ψ : Submodule.span (ZMod p) (Set.range y) →ₗ[ZMod p] ZMod p := b.constr (ZMod p) c with hψ
  obtain ⟨Ψ, hΨ⟩ := ψ.exists_extend
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot]
    exact hrad
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := φ)
      (Subspace.dual_finrank_eq (K := ZMod p) (V := V)).symm).mp hinj
  obtain ⟨v, hv⟩ := hsurj Ψ
  refine ⟨v, fun h => ?_⟩
  have h2 : Ψ ((b h : V)) = ψ (b h) := congrArg (fun T => T (b h)) hΨ
  have h3 : ((b h : V)) = y h := by
    rw [hb]
    exact congrArg Subtype.val (Module.Basis.span_apply hy h)
  rw [h3] at h2
  have h4 : Ψ (y h) = c h := by
    rw [h2, hψ, Module.Basis.constr_basis]
  rw [← h4, ← hv]

/-- Hyperbolic partners for an isotropic linearly independent family. -/
theorem exists_hyperbolic_partners [FiniteDimensional (ZMod p) V] (φ : AltForm p V)
    (hφ : IsAltForm φ) (hrad : formRadical φ = ⊥) {d : ℕ} (y : Fin d → V)
    (hy : LinearIndependent (ZMod p) y) (hiso : ∀ i h, φ (y i) (y h) = 0) :
    ∃ x : Fin d → V, (∀ i h, φ (x i) (y h) = if i = h then 1 else 0) ∧
      (∀ i h, i ≠ h → φ (x i) (x h) = 0) := by
  classical
  have aux : ∀ n : ℕ, ∃ x : Fin d → V,
      (∀ i : Fin d, (i : ℕ) < n → ∀ h, φ (x i) (y h) = if i = h then 1 else 0) ∧
      (∀ i h : Fin d, (i : ℕ) < n → (h : ℕ) < n → i ≠ h → φ (x i) (x h) = 0) := by
    intro n
    induction n with
    | zero => exact ⟨fun _ => 0, fun i hi => absurd hi (by omega), fun i h hi => absurd hi (by omega)⟩
    | succ n ih =>
      obtain ⟨x, hx1, hx2⟩ := ih
      by_cases hn : n < d
      · set m : Fin d := ⟨n, hn⟩ with hm
        obtain ⟨z, hz⟩ := exists_dual_vector φ hrad y hy (fun h => if m = h then 1 else 0)
        set T : Finset (Fin d) := Finset.univ.filter (fun k : Fin d => (k : ℕ) < n) with hT
        set xn : V := z + ∑ k ∈ T, (φ z (x k)) • y k with hxn
        refine ⟨Function.update x m xn, ?_, ?_⟩
        · intro i hi h
          rcases eq_or_ne i m with rfl | hne
          · rw [Function.update_self]
            have : φ xn (y h) = φ z (y h) := by
              simp only [hxn, map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply,
                map_smul, LinearMap.smul_apply, hiso, smul_zero, Finset.sum_const_zero, add_zero]
            rw [this, hz h]
          · rw [Function.update_of_ne hne]
            have hilt : (i : ℕ) < n := by
              have : (i : ℕ) ≠ n := by
                intro hcon
                exact hne (Fin.ext hcon)
              omega
            exact hx1 i hilt h
        · have hxnx : ∀ h : Fin d, (h : ℕ) < n → φ xn (x h) = 0 := by
            intro h hh
            have hmem : h ∈ T := by simp [hT, hh]
            have hterm : ∀ k ∈ T, (φ z (x k)) * (φ (y k) (x h))
                = if k = h then - φ z (x h) else 0 := by
              intro k hk
              have hkn : (k : ℕ) < n := by simpa [hT] using hk
              have h1 : φ (y k) (x h) = - φ (x h) (y k) := alt_skew hφ _ _
              rw [h1, hx1 h hh k]
              rcases eq_or_ne k h with rfl | hkh
              · simp
              · simp [hkh, Ne.symm hkh]
            have hsum : ∑ k ∈ T, (φ z (x k)) * (φ (y k) (x h)) = - φ z (x h) := by
              rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' T h]
              simp [hmem]
            simp only [hxn, map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply,
              map_smul, LinearMap.smul_apply, smul_eq_mul]
            rw [hsum]
            ring
          have hmn : ((m : Fin d) : ℕ) = n := rfl
          intro i h hi hh hih
          by_cases hne1 : i = m
          · have hhm : h ≠ m := by
              intro hc
              exact hih (hne1.trans hc.symm)
            have hh' : (h : ℕ) < n := by
              have hne : (h : ℕ) ≠ n := fun hc => hhm (Fin.ext (by rw [hc, hmn]))
              omega
            rw [hne1, Function.update_self, Function.update_of_ne hhm]
            exact hxnx h hh'
          · have hi' : (i : ℕ) < n := by
              have hne : (i : ℕ) ≠ n := fun hc => hne1 (Fin.ext (by rw [hc, hmn]))
              omega
            by_cases hne2 : h = m
            · rw [hne2, Function.update_self, Function.update_of_ne hne1]
              rw [alt_skew hφ (x i) xn, hxnx i hi', neg_zero]
            · have hh' : (h : ℕ) < n := by
                have hne : (h : ℕ) ≠ n := fun hc => hne2 (Fin.ext (by rw [hc, hmn]))
                omega
              rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
              exact hx2 i h hi' hh' hih
      · exact ⟨x, fun i _ h => hx1 i (lt_of_lt_of_le i.isLt (not_lt.mp hn)) h,
          fun i h _ _ hih => hx2 i h (lt_of_lt_of_le i.isLt (not_lt.mp hn))
            (lt_of_lt_of_le h.isLt (not_lt.mp hn)) hih⟩
  obtain ⟨x, hx1, hx2⟩ := aux d
  exact ⟨x, fun i h => hx1 i i.2 h, fun i h hih => hx2 i h i.2 h.2 hih⟩


theorem centralFactorSeries_K_mono {q : ℕ} [Fact q.Prime] {P : Type} [Group P]
    (S : CentralFactorSeries q P) : ∀ {a b : ℕ}, a ≤ b → S.K a ≤ S.K b := by
  intro a b hab
  induction b with
  | zero =>
    have : a = 0 := by omega
    rw [this]
  | succ n ih =>
    rcases Nat.lt_or_ge a (n + 1) with h | h
    · exact le_trans (ih (by omega)) (S.K_le n)
    · have : a = n + 1 := by omega
      rw [this]

theorem descentBranch_A_anti {q : ℕ} [Fact q.Prime] {P : Type} [Group P]
    {S : CentralFactorSeries q P} (Br : DescentBranch q P S) :
    ∀ {a b : ℕ}, a ≤ b → Br.A b ≤ Br.A a := by
  intro a b hab
  induction b with
  | zero =>
    have : a = 0 := by omega
    rw [this]
  | succ n ih =>
    rcases Nat.lt_or_ge a (n + 1) with h | h
    · exact le_trans (Br.A_le n) (ih (by omega))
    · have : a = n + 1 := by omega
      rw [this]

/-- **Lemma 5.4** (Transversal interaction clique): `d + 1` elements of `A_j` in pairwise distinct
cosets of `A_k`, whose commutators survive modulo `K_{L-j-1}`.  (The hypothesis `1 ≤ d` is
part of the statement in the manuscript, but it is not needed by the formal derivation.) -/
theorem transversal_interaction_clique {q : ℕ} [Fact q.Prime] {P : Type} [Group P] [Finite P]
    {S : CentralFactorSeries q P} (Br : DescentBranch q P S) (j k d : ℕ) (hj : j < S.L)
    (hjk : j < k) (_hd : 1 ≤ d) (hdt : d ≤ interRank Br j k) :
    ∃ a : Fin (d + 1) → P, (∀ i, a i ∈ Br.A j) ∧
      (∀ i i', i ≠ i' → (a i)⁻¹ * a i' ∉ Br.A k) ∧
      (∀ i i', i ≠ i' → ⁅a i, a i'⁆ ∉ S.K (S.L - j - 1)) := by
  classical
  have : Fact (1 < q) := ⟨(Fact.out : q.Prime).one_lt⟩
  set V := Fin (Br.rho j) → ZMod q
  set φ : AltForm q V := Br.f j with hφdef
  have hφ : IsAltForm φ := Br.f_alt j
  have hrad : formRadical φ = ⊥ := Br.f_nondeg j hj
  set Usp : Submodule (ZMod q) V :=
    Submodule.span (ZMod q) (Br.pr j '' (Br.A k : Set P)) with hUsp
  have hAk : Br.A k ≤ Br.A j := descentBranch_A_anti Br (le_of_lt hjk)
  -- the image of `A k` is isotropic
  have hcommk : ∀ x ∈ Br.A k, ∀ y ∈ Br.A k, ⁅x, y⁆ ∈ S.K (S.L - j - 1) := by
    intro x hx y hy
    rcases Nat.lt_or_ge S.L k with hk | hk
    · have hx' : x ∈ Br.A S.L := descentBranch_A_anti Br (le_of_lt hk) hx
      have hy' : y ∈ Br.A S.L := descentBranch_A_anti Br (le_of_lt hk) hy
      have : ⁅x, y⁆ = 1 := commutatorElement_eq_one_iff_commute.mpr (Br.leaf_abelian x hx' y hy')
      rw [this]
      exact Subgroup.one_mem _
    · have h1 : ⁅x, y⁆ ∈ S.K (S.L - k) :=
        Br.A_der k hk (Subgroup.commutator_mem_commutator hx hy)
      exact centralFactorSeries_K_mono S (by omega) h1
  have hisoU : IsIsotropic φ Usp := by
    refine isotropic_span φ _ ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact (Br.f_comm j hj x (hAk hx) y (hAk hy)).mpr (hcommk x hx y hy)
  -- a linearly independent isotropic family of size `d`
  have : FiniteDimensional (ZMod q) V := by infer_instance
  set bU := Module.finBasis (ZMod q) Usp with hbU
  set y : Fin d → V := fun i => (bU (Fin.castLE hdt i) : V) with hy
  have hymem : ∀ i, y i ∈ Usp := fun i => (bU (Fin.castLE hdt i)).2
  have hyli : LinearIndependent (ZMod q) y := by
    have h1 : LinearIndependent (ZMod q) (fun i : Fin d => bU (Fin.castLE hdt i)) :=
      bU.linearIndependent.comp _ (Fin.castLE_injective hdt)
    exact h1.map' Usp.subtype (by simp)
  have hyiso : ∀ i h, φ (y i) (y h) = 0 := fun i h => hisoU _ (hymem i) _ (hymem h)
  obtain ⟨x, hxy, hxx⟩ := exists_hyperbolic_partners φ hφ hrad y hyli hyiso
  have hxx0 : ∀ i, φ (x i) (x i) = 0 := fun i => hφ (x i)
  have hyx : ∀ i r : Fin d, φ (y i) (x r) = - (if r = i then 1 else 0) := by
    intro i r
    rw [alt_skew hφ (y i) (x r), hxy r i]
  have hxxall : ∀ i r : Fin d, φ (x i) (x r) = 0 := by
    intro i r
    rcases eq_or_ne i r with rfl | h
    · exact hxx0 i
    · exact hxx i r h
  have hsumyx : ∀ (s : Finset (Fin d)) (r : Fin d),
      ∑ h ∈ s, φ (y h) (x r) = -(if r ∈ s then 1 else 0) := by
    intro s r
    have hcong : ∀ h ∈ s, φ (y h) (x r) = -(if r = h then 1 else 0) := fun h _ => hyx h r
    rw [Finset.sum_congr rfl hcong, Finset.sum_neg_distrib, Finset.sum_ite_eq]
  have hsumyy : ∀ (s : Finset (Fin d)) (c : Fin d), ∑ h ∈ s, φ (y h) (y c) = 0 := by
    intro s c
    exact Finset.sum_eq_zero (fun h _ => hyiso h c)
  set w : Fin (d + 1) → V := fun i =>
    if h : (i : ℕ) < d then x ⟨i, h⟩ + ∑ h' ∈ Finset.Iio (⟨i, h⟩ : Fin d), y h'
    else ∑ h' : Fin d, y h' with hwdef
  have hwy : ∀ (i : Fin (d + 1)) (c : Fin d),
      φ (w i) (y c) = if (i : ℕ) = (c : ℕ) then 1 else 0 := by
    intro i c
    by_cases hi : (i : ℕ) < d
    · have h1 : φ (w i) (y c)
          = φ (x ⟨i, hi⟩) (y c) + ∑ h' ∈ Finset.Iio (⟨i, hi⟩ : Fin d), φ (y h') (y c) := by
        simp only [hwdef, dite_eq_left hi, map_add, LinearMap.add_apply, map_sum,
          LinearMap.sum_apply]
      rw [h1, hsumyy, add_zero, hxy]
      exact if_congr (by simp [Fin.ext_iff]) rfl rfl
    · have h1 : φ (w i) (y c) = ∑ h' : Fin d, φ (y h') (y c) := by
        simp only [hwdef, dite_eq_right hi, map_sum, LinearMap.sum_apply]
      rw [h1, hsumyy]
      have : (i : ℕ) ≠ (c : ℕ) := by
        have := c.isLt
        omega
      rw [ite_eq_right this]
  have hwx : ∀ (i : Fin (d + 1)) (r : Fin d),
      φ (w i) (x r) = -(if (r : ℕ) < (i : ℕ) then 1 else 0) := by
    intro i r
    by_cases hi : (i : ℕ) < d
    · have h1 : φ (w i) (x r)
          = φ (x ⟨i, hi⟩) (x r) + ∑ h' ∈ Finset.Iio (⟨i, hi⟩ : Fin d), φ (y h') (x r) := by
        simp only [hwdef, dite_eq_left hi, map_add, LinearMap.add_apply, map_sum,
          LinearMap.sum_apply]
      rw [h1, hxxall, zero_add, hsumyx]
      congr 2
      simp [Finset.mem_Iio, Fin.lt_def]
    · have h1 : φ (w i) (x r) = ∑ h' : Fin d, φ (y h') (x r) := by
        simp only [hwdef, dite_eq_right hi, map_sum, LinearMap.sum_apply]
      rw [h1, hsumyx]
      have hr : (r : ℕ) < (i : ℕ) := by
        have := r.isLt
        omega
      simp [hr]
  have hsumwy1 : ∀ (i : Fin (d + 1)) (hi : (i : ℕ) < d) (s : Finset (Fin d)),
      ∑ h ∈ s, φ (w i) (y h) = if (⟨i, hi⟩ : Fin d) ∈ s then 1 else 0 := by
    intro i hi s
    have hcong : ∀ h ∈ s, φ (w i) (y h) = if (⟨i, hi⟩ : Fin d) = h then 1 else 0 := by
      intro h _
      rw [hwy i h]
      exact if_congr (by simp [Fin.ext_iff]) rfl rfl
    rw [Finset.sum_congr rfl hcong, Finset.sum_ite_eq]
  have hsumwy2 : ∀ (i : Fin (d + 1)), ¬ (i : ℕ) < d → ∀ (s : Finset (Fin d)),
      ∑ h ∈ s, φ (w i) (y h) = 0 := by
    intro i hi s
    refine Finset.sum_eq_zero (fun h _ => ?_)
    rw [hwy i h]
    have : (i : ℕ) ≠ (h : ℕ) := by
      have := h.isLt
      omega
    rw [ite_eq_right this]
  have hww : ∀ i i' : Fin (d + 1), i ≠ i' → φ (w i) (w i') ≠ 0 := by
    intro i i' hne
    have hnenat : (i : ℕ) ≠ (i' : ℕ) := fun hc => hne (Fin.ext hc)
    by_cases hi' : (i' : ℕ) < d
    · have h1 : φ (w i) (w i')
          = φ (w i) (x ⟨i', hi'⟩) + ∑ h' ∈ Finset.Iio (⟨i', hi'⟩ : Fin d), φ (w i) (y h') := by
        simp only [hwdef, dite_eq_left hi', map_add, map_sum]
      by_cases hi : (i : ℕ) < d
      · rw [h1, hwx, hsumwy1 i hi]
        rcases Nat.lt_or_ge (i : ℕ) (i' : ℕ) with hlt | hge
        · have e1 : ¬ ((i' : ℕ) < (i : ℕ)) := by omega
          have e2 : (⟨i, hi⟩ : Fin d) ∈ Finset.Iio (⟨i', hi'⟩ : Fin d) := by
            simp [Finset.mem_Iio, Fin.lt_def, hlt]
          rw [ite_eq_right e1, ite_eq_left e2]
          simp
        · have hgt : (i' : ℕ) < (i : ℕ) := by omega
          have e2 : (⟨i, hi⟩ : Fin d) ∉ Finset.Iio (⟨i', hi'⟩ : Fin d) := by
            simp only [Finset.mem_Iio, Fin.lt_def, not_lt]
            omega
          rw [ite_eq_left hgt, ite_eq_right e2]
          simp
      · rw [h1, hwx, hsumwy2 i hi]
        have hgt : (i' : ℕ) < (i : ℕ) := by
          have := i.isLt
          omega
        rw [ite_eq_left hgt]
        simp
    · have h1 : φ (w i) (w i') = ∑ h' : Fin d, φ (w i) (y h') := by
        simp only [hwdef, dite_eq_right hi', map_sum]
      have hi : (i : ℕ) < d := by
        have := i.isLt
        have := i'.isLt
        omega
      rw [h1, hsumwy1 i hi, ite_eq_left (Finset.mem_univ _)]
      exact one_ne_zero
  -- lift to group elements
  have hpr1 : Br.pr j 1 = 0 := by
    have h := Br.pr_mul j 1 (Br.A j).one_mem 1 (Br.A j).one_mem
    rw [mul_one] at h
    linear_combination (norm := module) -h
  have hprinv : ∀ z ∈ Br.A j, Br.pr j z⁻¹ = - Br.pr j z := by
    intro z hz
    have h := Br.pr_mul j z hz z⁻¹ ((Br.A j).inv_mem hz)
    rw [mul_inv_cancel, hpr1] at h
    linear_combination (norm := module) -h
  choose a haA hapr using fun i : Fin (d + 1) => Br.pr_surj j hj (w i)
  refine ⟨a, haA, ?_, ?_⟩
  · intro i i' hne hmem
    have hnenat : (i : ℕ) ≠ (i' : ℕ) := fun hc => hne (Fin.ext hc)
    have h1 : Br.pr j ((a i)⁻¹ * a i') ∈ Usp :=
      Submodule.subset_span ⟨(a i)⁻¹ * a i', hmem, rfl⟩
    have h2 : Br.pr j ((a i)⁻¹ * a i') = - w i + w i' := by
      rw [Br.pr_mul j _ ((Br.A j).inv_mem (haA i)) _ (haA i'), hprinv _ (haA i),
        hapr i, hapr i']
    rw [h2] at h1
    have h3 : ∀ c : Fin d, φ (- w i + w i') (y c) = 0 :=
      fun c => hisoU _ h1 _ (hymem c)
    by_cases hi : (i : ℕ) < d
    · have h4 := h3 ⟨i, hi⟩
      rw [map_add, LinearMap.add_apply, map_neg, LinearMap.neg_apply, hwy i, hwy i'] at h4
      rw [ite_eq_left rfl, ite_eq_right (by simpa using hnenat.symm)] at h4
      simp at h4
    · have hi' : (i' : ℕ) < d := by
        have := i.isLt
        have := i'.isLt
        omega
      have h4 := h3 ⟨i', hi'⟩
      rw [map_add, LinearMap.add_apply, map_neg, LinearMap.neg_apply, hwy i, hwy i'] at h4
      rw [ite_eq_left rfl, ite_eq_right (by simpa using hnenat)] at h4
      simp at h4
  · intro i i' hne hmem
    have h := (Br.f_comm j hj (a i) (haA i) (a i') (haA i')).mpr hmem
    rw [hapr i, hapr i'] at h
    exact hww i i' hne h


/-- The restriction of a form to a subspace. -/
def formRestrict (φ : AltForm p V) (W : Submodule (ZMod p) V) : AltForm p W :=
  LinearMap.compl₁₂ φ W.subtype W.subtype

@[simp] theorem formRestrict_apply (φ : AltForm p V) (W : Submodule (ZMod p) V) (x y : W) :
    formRestrict φ W x y = φ x y := rfl

theorem formRestrict_isAlt {φ : AltForm p V} (hφ : IsAltForm φ) (W : Submodule (ZMod p) V) :
    IsAltForm (formRestrict φ W) := fun x => hφ x

/-- Restricting a form to a subspace of codimension `c` decreases its rank by at most `2c`. -/
theorem formRank_restrict_ge [FiniteDimensional (ZMod p) V] (φ : AltForm p V)
    (W : Submodule (ZMod p) V) :
    formRank φ ≤ formRank (formRestrict φ W)
      + 2 * (Module.finrank (ZMod p) V - Module.finrank (ZMod p) W) := by
  classical
  set perp : Submodule (ZMod p) V := Submodule.comap φ W.dualAnnihilator with hperp
  have hcomap : Module.finrank (ZMod p) perp
      ≤ Module.finrank (ZMod p) (LinearMap.ker φ)
        + Module.finrank (ZMod p) W.dualAnnihilator := by
    set g := φ.domRestrict perp with hg
    have h1 : Module.finrank (ZMod p) (LinearMap.range g)
        + Module.finrank (ZMod p) (LinearMap.ker g)
        = Module.finrank (ZMod p) perp := LinearMap.finrank_range_add_finrank_ker g
    have h2 : Module.finrank (ZMod p) (LinearMap.ker g)
        ≤ Module.finrank (ZMod p) (LinearMap.ker φ) := by
      have he := Submodule.equivMapOfInjective (perp.subtype) (Submodule.injective_subtype _)
        (LinearMap.ker g)
      have h5 : (LinearMap.ker g).map (perp.subtype) ≤ LinearMap.ker φ := by
        rintro _ ⟨⟨x, hx⟩, hker, rfl⟩
        simpa [hg, LinearMap.mem_ker, LinearMap.domRestrict_apply] using hker
      calc Module.finrank (ZMod p) (LinearMap.ker g)
            = Module.finrank (ZMod p) ((LinearMap.ker g).map (perp.subtype)) := he.finrank_eq
        _ ≤ Module.finrank (ZMod p) (LinearMap.ker φ) := Submodule.finrank_mono h5
    have h3 : LinearMap.range g ≤ W.dualAnnihilator := by
      rintro _ ⟨⟨x, hx⟩, rfl⟩
      exact hx
    have h4 : Module.finrank (ZMod p) (LinearMap.range g)
        ≤ Module.finrank (ZMod p) W.dualAnnihilator := Submodule.finrank_mono h3
    omega
  have hann : Module.finrank (ZMod p) W + Module.finrank (ZMod p) W.dualAnnihilator
      = Module.finrank (ZMod p) V := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have hrad : Module.finrank (ZMod p) (formRadical (formRestrict φ W))
      ≤ Module.finrank (ZMod p) perp := by
    have he := Submodule.equivMapOfInjective (W.subtype) (Submodule.injective_subtype _)
      (formRadical (formRestrict φ W))
    have h5 : (formRadical (formRestrict φ W)).map (W.subtype) ≤ perp := by
      rintro _ ⟨⟨x, hx⟩, hker, rfl⟩
      rw [hperp, Submodule.mem_comap, Submodule.mem_dualAnnihilator]
      intro y hy
      have := congrArg (fun (f : W →ₗ[ZMod p] ZMod p) => f ⟨y, hy⟩) hker
      simpa [formRestrict] using this
    calc Module.finrank (ZMod p) (formRadical (formRestrict φ W))
          = Module.finrank (ZMod p) ((formRadical (formRestrict φ W)).map (W.subtype)) :=
            he.finrank_eq
      _ ≤ Module.finrank (ZMod p) perp := Submodule.finrank_mono h5
  have hWV : Module.finrank (ZMod p) W ≤ Module.finrank (ZMod p) V := Submodule.finrank_le W
  have hRV : Module.finrank (ZMod p) (formRadical φ) ≤ Module.finrank (ZMod p) V :=
    Submodule.finrank_le _
  have hSW : Module.finrank (ZMod p) (formRadical (formRestrict φ W))
      ≤ Module.finrank (ZMod p) W := Submodule.finrank_le _
  simp only [formRank, formRadical] at *
  have hAnn : Module.finrank (ZMod p) W.dualAnnihilator =
      Module.finrank (ZMod p) V - Module.finrank (ZMod p) W := by
    omega
  have hSR : Module.finrank (ZMod p) (LinearMap.ker (formRestrict φ W)) ≤
      Module.finrank (ZMod p) (LinearMap.ker φ) +
        (Module.finrank (ZMod p) V - Module.finrank (ZMod p) W) :=
    calc
      _ ≤ Module.finrank (ZMod p) perp := hrad
      _ ≤ Module.finrank (ZMod p) (LinearMap.ker φ) +
          Module.finrank (ZMod p) W.dualAnnihilator := hcomap
      _ = _ := by rw [hAnn]
  have nat_ineq : ∀ v r w s : ℕ, w ≤ v → r ≤ v → s ≤ w → s ≤ r + (v - w) →
      v - r ≤ w - s + 2 * (v - w) := by
    omega
  exact nat_ineq _ _ _ _ hWV hRV hSW hSR

/-- If a subgroup `H` of the stage subgroup `A_k` has index at most `q^m` in `A_k`, then its
image in the stage symplectic space is a subspace of codimension at most `m`. -/
theorem stage_image_codim {q : ℕ} [Fact q.Prime] {P : Type} [Group P] [Finite P]
    {S : CentralFactorSeries q P} (Br : DescentBranch q P S) (k : ℕ) (hk : k < S.L)
    (H : Subgroup P) (hH : H ≤ Br.A k) (m : ℕ) (hidx : H.relIndex (Br.A k) ≤ q ^ m) :
    ∃ W : Submodule (ZMod q) (Fin (Br.rho k) → ZMod q),
      (∀ w, w ∈ W ↔ ∃ x ∈ H, Br.pr k x = w) ∧
      Module.finrank (ZMod q) (Fin (Br.rho k) → ZMod q) ≤ Module.finrank (ZMod q) W + m := by
  classical
  have hq : q.Prime := Fact.out
  have : NeZero q := ⟨hq.ne_zero⟩
  have hpr1 : Br.pr k 1 = 0 := by
    have h := Br.pr_mul k 1 (Br.A k).one_mem 1 (Br.A k).one_mem
    rw [mul_one] at h
    linear_combination (norm := module) -h
  have hpow : ∀ (n : ℕ) (x : P), x ∈ Br.A k → Br.pr k (x ^ n) = n • Br.pr k x := by
    intro n
    induction n with
    | zero => intro x _; simpa using hpr1
    | succ n ih =>
      intro x hx
      rw [pow_succ, Br.pr_mul k _ ((Br.A k).pow_mem hx n) _ hx, ih x hx, succ_nsmul]
  set W : Submodule (ZMod q) (Fin (Br.rho k) → ZMod q) :=
    { carrier := Br.pr k '' (H : Set P)
      zero_mem' := ⟨1, H.one_mem, hpr1⟩
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x * y, H.mul_mem hx hy, Br.pr_mul k _ (hH hx) _ (hH hy)⟩
      smul_mem' := by
        rintro c _ ⟨x, hx, rfl⟩
        refine ⟨x ^ c.val, H.pow_mem hx _, ?_⟩
        rw [hpow _ x (hH hx), ← Nat.cast_smul_eq_nsmul (ZMod q),
          ZMod.natCast_rightInverse c] } with hWdef
  refine ⟨W, fun w => Iff.rfl, ?_⟩
  -- the induced surjection of `A_k` onto the quotient space
  set F : ↥(Br.A k) →* Multiplicative ((Fin (Br.rho k) → ZMod q) ⧸ W) :=
    MonoidHom.mk' (fun x => Multiplicative.ofAdd (W.mkQ (Br.pr k (x : P)))) (by
      intro x y
      have h := Br.pr_mul k (x : P) x.2 (y : P) y.2
      simp only [Subgroup.coe_mul, h, map_add]
      rfl) with hFdef
  have hFsurj : Function.Surjective F := by
    intro z
    obtain ⟨v, hv⟩ := W.mkQ_surjective (Multiplicative.toAdd z)
    obtain ⟨x, hx, hxv⟩ := Br.pr_surj k hk v
    refine ⟨⟨x, hx⟩, ?_⟩
    simp only [hFdef, MonoidHom.mk'_apply, hxv, hv]
    rfl
  have hker : H.subgroupOf (Br.A k) ≤ F.ker := by
    intro x hx
    have hxH : (x : P) ∈ H := hx
    have hmem : Br.pr k (x : P) ∈ W := ⟨(x : P), hxH, rfl⟩
    simp only [MonoidHom.mem_ker, hFdef, MonoidHom.mk'_apply]
    have : W.mkQ (Br.pr k (x : P)) = 0 := (Submodule.Quotient.mk_eq_zero W).mpr hmem
    rw [this]
    rfl
  have : Finite ↥(Br.A k) := inferInstance
  have hkerne : (H.subgroupOf (Br.A k)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hidxker : F.ker.index ≤ q ^ m := by
    have hdvd : F.ker.index ∣ (H.subgroupOf (Br.A k)).index := Subgroup.index_dvd_of_le hker
    have hle : F.ker.index ≤ (H.subgroupOf (Br.A k)).index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hkerne) hdvd
    exact le_trans hle hidx
  have hcardQ : Nat.card ((Fin (Br.rho k) → ZMod q) ⧸ W) = F.ker.index := by
    have h1 : F.ker.index = Nat.card ↥(Subgroup.map F ⊤) := by
      rw [← Subgroup.relIndex_top_right, Subgroup.relIndex_ker]
    have h2 : Subgroup.map F ⊤ = ⊤ := by
      rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
      exact hFsurj
    calc Nat.card ((Fin (Br.rho k) → ZMod q) ⧸ W)
        = Nat.card (Multiplicative ((Fin (Br.rho k) → ZMod q) ⧸ W)) :=
          Nat.card_congr Multiplicative.ofAdd
      _ = Nat.card ↥(⊤ : Subgroup (Multiplicative ((Fin (Br.rho k) → ZMod q) ⧸ W))) :=
          (Nat.card_congr (Subgroup.topEquiv).toEquiv).symm
      _ = F.ker.index := by rw [h1, h2]
  have : Fintype ((Fin (Br.rho k) → ZMod q) ⧸ W) := Fintype.ofFinite _
  have hpowcard : Fintype.card ((Fin (Br.rho k) → ZMod q) ⧸ W)
      = q ^ Module.finrank (ZMod q) ((Fin (Br.rho k) → ZMod q) ⧸ W) := by
    rw [Module.card_eq_pow_finrank (K := ZMod q)]
    simp [ZMod.card]
  have hquot : Module.finrank (ZMod q) ((Fin (Br.rho k) → ZMod q) ⧸ W)
      + Module.finrank (ZMod q) W = Module.finrank (ZMod q) (Fin (Br.rho k) → ZMod q) :=
    Submodule.finrank_quotient_add_finrank W
  have hle : q ^ Module.finrank (ZMod q) ((Fin (Br.rho k) → ZMod q) ⧸ W) ≤ q ^ m := by
    rw [← hpowcard, ← Nat.card_eq_fintype_card, hcardQ]
    exact hidxker
  have hexp : Module.finrank (ZMod q) ((Fin (Br.rho k) → ZMod q) ⧸ W) ≤ m :=
    (Nat.pow_le_pow_iff_right hq.one_lt).mp hle
  omega

/-- The rank of the stage form is the stage rank. -/
theorem formRank_stage {q : ℕ} [Fact q.Prime] {P : Type} [Group P]
    {S : CentralFactorSeries q P} (Br : DescentBranch q P S) (j : ℕ) (hj : j < S.L) :
    formRank (Br.f j) = Br.rho j := by
  have h1 : formRadical (Br.f j) = ⊥ := Br.f_nondeg j hj
  rw [formRank, h1]
  simp

section NestedAnchor

variable {q : ℕ} [Fact q.Prime] {P : Type} [Group P]
  {S : CentralFactorSeries q P}

theorem pr_one (Br : DescentBranch q P S) (j : ℕ) : Br.pr j 1 = 0 := by
  have h := Br.pr_mul j 1 (Br.A j).one_mem 1 (Br.A j).one_mem
  rw [mul_one] at h
  linear_combination (norm := module) -h

theorem pr_inv (Br : DescentBranch q P S) (j : ℕ) {z : P} (hz : z ∈ Br.A j) :
    Br.pr j z⁻¹ = - Br.pr j z := by
  have h := Br.pr_mul j z hz z⁻¹ ((Br.A j).inv_mem hz)
  rw [mul_inv_cancel, pr_one] at h
  linear_combination (norm := module) -h

/-- The kernel of the stage-`j` projection, as a subgroup of the stage-`j` subgroup. -/
def prKer (Br : DescentBranch q P S) (j : ℕ) : Subgroup P where
  carrier := {x | x ∈ Br.A j ∧ Br.pr j x = 0}
  one_mem' := ⟨(Br.A j).one_mem, pr_one Br j⟩
  mul_mem' := by
    rintro x y ⟨hx, hx0⟩ ⟨hy, hy0⟩
    exact ⟨(Br.A j).mul_mem hx hy, by rw [Br.pr_mul j x hx y hy, hx0, hy0, add_zero]⟩
  inv_mem' := by
    rintro x ⟨hx, hx0⟩
    exact ⟨(Br.A j).inv_mem hx, by rw [pr_inv Br j hx, hx0, neg_zero]⟩

@[simp] theorem mem_prKer (Br : DescentBranch q P S) (j : ℕ) (x : P) :
    x ∈ prKer Br j ↔ x ∈ Br.A j ∧ Br.pr j x = 0 := Iff.rfl

variable [Finite P]

omit [Finite P] in
/-- The kernel of the stage-`j` projection has relative index at most `q ^ t_{j,k}` in `A_k`. -/
theorem prKer_relIndex_le (Br : DescentBranch q P S) (j k : ℕ) (hle : Br.A k ≤ Br.A j) :
    (prKer Br j).relIndex (Br.A k) ≤ q ^ interRank Br j k := by
  classical
  have hq : q.Prime := Fact.out
  have : NeZero q := ⟨hq.ne_zero⟩
  set M : Submodule (ZMod q) (Fin (Br.rho j) → ZMod q) :=
    Submodule.span (ZMod q) (Br.pr j '' (Br.A k : Set P)) with hM
  set F : ↥(Br.A k) →* Multiplicative (Fin (Br.rho j) → ZMod q) :=
    MonoidHom.mk' (fun x => Multiplicative.ofAdd (Br.pr j (x : P))) (by
      intro x y
      have h := Br.pr_mul j (x : P) (hle x.2) (y : P) (hle y.2)
      simp only [Subgroup.coe_mul, h]
      rfl) with hF
  have hker : F.ker = (prKer Br j).subgroupOf (Br.A k) := by
    ext x
    constructor
    · intro hx
      have hx' : Br.pr j (x : P) = 0 := hx
      exact ⟨hle x.2, hx'⟩
    · intro hx
      have hx' : Br.pr j (x : P) = 0 := hx.2
      show Multiplicative.ofAdd (Br.pr j (x : P)) = 1
      rw [hx']
      rfl
  have hidx : (prKer Br j).relIndex (Br.A k) = Nat.card ↥(Subgroup.map F ⊤) := by
    have h1 : (prKer Br j).relIndex (Br.A k) = ((prKer Br j).subgroupOf (Br.A k)).index := rfl
    rw [h1, ← hker, ← Subgroup.relIndex_top_right, Subgroup.relIndex_ker]
  have hsub : ∀ y ∈ Subgroup.map F ⊤, Multiplicative.toAdd y ∈ M := by
    rintro _ ⟨x, -, rfl⟩
    exact Submodule.subset_span ⟨(x : P), x.2, rfl⟩
  have hcard : Nat.card ↥(Subgroup.map F ⊤) ≤ Nat.card ↥M := by
    refine Nat.card_le_card_of_injective
      (fun y : ↥(Subgroup.map F ⊤) => (⟨Multiplicative.toAdd (y : _), hsub _ y.2⟩ : ↥M)) ?_
    intro a b hab
    exact Subtype.ext (by simpa using congrArg Subtype.val hab)
  have : Fintype ↥M := Fintype.ofFinite _
  have hMcard : Nat.card ↥M = q ^ interRank Br j k := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod q), ZMod.card, hM]
    rfl
  omega

/-- A clique of stage-`k` elements inside a subgroup of small relative index. -/
theorem stage_clique_exists (Br : DescentBranch q P S) (k : ℕ) (hk : k < S.L)
    (Hs : Subgroup P) (hHsA : Hs ≤ Br.A k) (m : ℕ) (hrel : Hs.relIndex (Br.A k) ≤ q ^ m) :
    ∃ C : Finset P, (∀ x ∈ C, x ∈ Hs) ∧ C.Nonempty ∧
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → ⁅x, y⁆ ∉ S.K (S.L - k - 1)) ∧
      1 + (kappa q * ((Br.rho k : ℝ) - 2 * m) - cc q) ≤ (C.card : ℝ) := by
  classical
  have hq : q.Prime := Fact.out
  have hkap : (0:ℝ) ≤ kappa q := le_of_lt (kappa_pos hq.two_le)
  obtain ⟨W, hWmem, hWcodim⟩ := stage_image_codim Br k hk Hs hHsA m hrel
  have hrank : Br.rho k ≤ formRank (formRestrict (Br.f k) W) + 2 * m := by
    have h1 := formRank_restrict_ge (Br.f k) W
    rw [formRank_stage Br k hk] at h1
    omega
  obtain ⟨D, hD, hDcard⟩ :=
    scalar_clique_credit (formRestrict (Br.f k) W) (formRestrict_isAlt (Br.f_alt k) W)
  have hkey : kappa q * ((Br.rho k : ℝ) - 2 * m) - cc q ≤ (D.card : ℝ) - 1 := by
    have h2 : ((Br.rho k : ℝ) - 2 * m) ≤ (formRank (formRestrict (Br.f k) W) : ℝ) := by
      have h4 : (Br.rho k : ℝ) ≤ (formRank (formRestrict (Br.f k) W) : ℝ) + 2 * m := by
        exact_mod_cast hrank
      linarith
    have h3 : kappa q * ((Br.rho k : ℝ) - 2 * m)
        ≤ kappa q * (formRank (formRestrict (Br.f k) W) : ℝ) :=
      mul_le_mul_of_nonneg_left h2 hkap
    linarith [hDcard]
  choose g hgH hgpr using fun w : {x // x ∈ W} => (hWmem (w : Fin (Br.rho k) → ZMod q)).mp w.2
  by_cases hDne : D.Nonempty
  · have hginj : Function.Injective g := by
      intro w w' h
      have h1 := hgpr w
      rw [h, hgpr w'] at h1
      exact Subtype.ext h1.symm
    refine ⟨D.image g, ?_, hDne.image g, ?_, ?_⟩
    · rintro x hx
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hx
      exact hgH w
    · rintro x hx y hy hxy
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨w', hw', rfl⟩ := Finset.mem_image.mp hy
      have hww' : w ≠ w' := fun h => hxy (by rw [h])
      have hphi : (Br.f k) (Br.pr k (g w)) (Br.pr k (g w')) ≠ 0 := by
        have h1 := hD w (Finset.mem_coe.mpr hw) w' (Finset.mem_coe.mpr hw') hww'
        rw [hgpr w, hgpr w']
        simpa [formRestrict] using h1
      intro hmem
      exact hphi ((Br.f_comm k hk (g w) (hHsA (hgH w)) (g w') (hHsA (hgH w'))).mpr hmem)
    · rw [Finset.card_image_of_injective _ hginj]
      linarith [hkey]
  · have hD0 : D.card = 0 := by
      rw [Finset.card_eq_zero]
      exact Finset.not_nonempty_iff_eq_empty.mp hDne
    refine ⟨{1}, ?_, ⟨1, by simp⟩, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_singleton.mp hx]
      exact Hs.one_mem
    · intro x hx y hy hxy
      rw [Finset.mem_singleton.mp hx, Finset.mem_singleton.mp hy] at hxy
      exact absurd rfl hxy
    · rw [hD0] at hkey
      simp only [Finset.card_singleton, Nat.cast_one]
      norm_num at hkey ⊢
      linarith

omit [Finite P] in
/-- The stage subgroups of a descent branch decrease. -/
theorem branch_A_antitone (Br : DescentBranch q P S) {i j : ℕ} (h : i ≤ j) :
    Br.A j ≤ Br.A i := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans (Br.A_le _) ih

omit [Finite P] in
/-- Two translates of a common element commute exactly when the translating factors do. -/
theorem commute_zmul_iff {z c d : P} (hc : Commute c z) (hd : Commute d z) :
    Commute (z * c) (z * d) ↔ Commute c d := by
  have e1 : z * c * (z * d) = z * z * (c * d) := by
    calc z * c * (z * d) = z * (c * z) * d := by group
      _ = z * (z * c) * d := by rw [hc.eq]
      _ = z * z * (c * d) := by group
  have e2 : z * d * (z * c) = z * z * (d * c) := by
    calc z * d * (z * c) = z * (d * z) * c := by group
      _ = z * (z * d) * c := by rw [hd.eq]
      _ = z * z * (d * c) := by group
  constructor
  · intro h
    have h3 := h.eq
    rw [e1, e2] at h3
    exact mul_left_cancel h3
  · intro h
    show z * c * (z * d) = z * d * (z * c)
    rw [e1, e2, h.eq]

/-- The nested-anchor construction of Lemma 5.5, run along an arbitrary increasing sequence of
stages. -/
theorem nested_stage_construction (Br : DescentBranch q P S) (kk : ℕ → ℕ)
    (hmono : StrictMono kk) (l B : ℕ)
    (hB : ∀ g : P, (Subgroup.centralizer ({g} : Set P)).index ≤ B)
    (hBq : B ≤ q ^ l) :
    ∀ m : ℕ, (∀ i, i < m → kk i < S.L) →
    ∃ (T : Finset P) (z : P) (an : ℕ → P),
      IsNoncommSet (T : Set P) ∧ z ∈ T ∧
      (∀ j, j < m → an j ∈ Br.A (kk j)) ∧
      (∀ j, j < m → ∀ j', j' < j → Br.pr (kk j') (an j) = 0 ∧ Commute (an j) (an j')) ∧
      (∀ u : P, (∀ j, j < m → Commute u (an j)) → Commute u z) ∧
      (∀ x ∈ T, x ≠ z → ∀ u : P,
        (∀ j, j < m → u ∈ Br.A (kk j) ∧ Br.pr (kk j) u = 0 ∧ Commute u (an j)) →
        ¬ Commute x (z * u)) ∧
      1 + ∑ i ∈ Finset.range m,
        (kappa q * ((Br.rho (kk i) : ℝ)
          - 2 * ((∑ j ∈ Finset.range i, (interRank Br (kk j) (kk i) : ℝ)) + i * l)) - cc q)
        ≤ (T.card : ℝ) := by
  classical
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨{1}, 1, fun _ => 1, ?_, Finset.mem_singleton_self 1, by omega, by omega, ?_, ?_, ?_⟩
    · intro x hx y hy hxy
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx hy
      exact absurd (hx.trans hy.symm) hxy
    · intro u _
      exact Commute.one_right u
    · intro x hx hxz
      exact absurd (Finset.mem_singleton.mp hx) hxz
    · simp
  | succ m ih =>
    intro hkkL
    obtain ⟨T, z, an, hnc, hzT, hanA, hanpr, hH4, hH5, hTcard⟩ :=
      ih (fun i hi => hkkL i (by omega))
    have hkL : kk m < S.L := hkkL m (by omega)
    -- the constrained stage subgroup
    set X : Subgroup P := ⨅ j : Fin m, (prKer Br (kk j) ⊓ Subgroup.centralizer ({an j} : Set P))
      with hXdef
    set Hs : Subgroup P := Br.A (kk m) ⊓ X with hHsdef
    have hHsA : Hs ≤ Br.A (kk m) := inf_le_left
    set mm : ℕ := (∑ j ∈ Finset.range m, interRank Br (kk j) (kk m)) + m * l with hmmdef
    have hrel : Hs.relIndex (Br.A (kk m)) ≤ q ^ mm := by
      have h1 : Hs.relIndex (Br.A (kk m)) = X.relIndex (Br.A (kk m)) :=
        Subgroup.inf_relIndex_left _ _
      have h2 := Subgroup.relIndex_iInf_le (L := Br.A (kk m))
        (fun j : Fin m => prKer Br (kk j) ⊓ Subgroup.centralizer ({an j} : Set P))
      have h3 : ∀ j : Fin m,
          (prKer Br (kk j) ⊓ Subgroup.centralizer ({an j} : Set P)).relIndex (Br.A (kk m))
            ≤ q ^ (interRank Br (kk j) (kk m) + l) := by
        intro j
        have hA : Br.A (kk m) ≤ Br.A (kk j) :=
          branch_A_antitone Br (le_of_lt (hmono j.isLt))
        have ha := prKer_relIndex_le Br (kk j) (kk m) hA
        have hne : (Subgroup.centralizer ({an j} : Set P)).relIndex ⊤ ≠ 0 := by
          rw [Subgroup.relIndex_top_right]
          exact Subgroup.index_ne_zero_of_finite
        have h4 := Subgroup.relIndex_le_of_le_right (le_top : Br.A (kk m) ≤ ⊤) hne
        rw [Subgroup.relIndex_top_right] at h4
        have hb : (Subgroup.centralizer ({an j} : Set P)).relIndex (Br.A (kk m)) ≤ q ^ l :=
          le_trans (le_trans h4 (hB _)) hBq
        calc (prKer Br (kk j) ⊓ Subgroup.centralizer ({an j} : Set P)).relIndex (Br.A (kk m))
            ≤ (prKer Br (kk j)).relIndex (Br.A (kk m))
              * (Subgroup.centralizer ({an j} : Set P)).relIndex (Br.A (kk m)) :=
              Subgroup.relIndex_inf_le
          _ ≤ q ^ interRank Br (kk j) (kk m) * q ^ l := Nat.mul_le_mul ha hb
          _ = q ^ (interRank Br (kk j) (kk m) + l) := (pow_add _ _ _).symm
      have h5 : (∏ j : Fin m,
          (prKer Br (kk j) ⊓ Subgroup.centralizer ({an j} : Set P)).relIndex (Br.A (kk m)))
          ≤ ∏ j : Fin m, q ^ (interRank Br (kk j) (kk m) + l) :=
        Finset.prod_le_prod' (fun j _ => h3 j)
      have h6 : (∏ j : Fin m, q ^ (interRank Br (kk j) (kk m) + l)) = q ^ mm := by
        rw [Finset.prod_pow_eq_pow_sum, hmmdef]
        congr 1
        rw [Finset.sum_add_distrib, Fin.sum_univ_eq_sum_range
          (fun j => interRank Br (kk j) (kk m)) m]
        simp [mul_comm]
      calc Hs.relIndex (Br.A (kk m)) = X.relIndex (Br.A (kk m)) := h1
        _ ≤ _ := h2
        _ ≤ _ := h5
        _ = q ^ mm := h6
    obtain ⟨C, hC1, hCne, hCcl, hCcard⟩ := stage_clique_exists Br (kk m) hkL Hs hHsA mm hrel
    -- membership facts for the new clique
    have hCmem : ∀ c ∈ C, c ∈ Br.A (kk m) ∧
        ∀ j, j < m → (Br.pr (kk j) c = 0 ∧ Commute c (an j)) := by
      intro c hc
      have hcHs := hC1 c hc
      rw [hHsdef, Subgroup.mem_inf] at hcHs
      refine ⟨hcHs.1, ?_⟩
      intro j hj
      have h1 := (Subgroup.mem_iInf.mp hcHs.2) (⟨j, hj⟩ : Fin m)
      rw [Subgroup.mem_inf] at h1
      refine ⟨h1.1.2, ?_⟩
      exact (Subgroup.mem_centralizer_iff.mp h1.2 (an j) (Set.mem_singleton _)).symm
    have hDc : ∀ c ∈ C, ∀ j, j < m →
        c ∈ Br.A (kk j) ∧ Br.pr (kk j) c = 0 ∧ Commute c (an j) := by
      intro c hc j hj
      obtain ⟨hcA, hrest⟩ := hCmem c hc
      exact ⟨branch_A_antitone Br (le_of_lt (hmono hj)) hcA, (hrest j hj).1, (hrest j hj).2⟩
    have hCz : ∀ c ∈ C, Commute c z := fun c hc =>
      hH4 c (fun j hj => (hDc c hc j hj).2.2)
    obtain ⟨a, haC⟩ := hCne
    set an' : ℕ → P := Function.update an m a with han'def
    have han'lt : ∀ j, j < m → an' j = an j := by
      intro j hj
      rw [han'def, Function.update_of_ne (by omega)]
    have han'm : an' m = a := by rw [han'def, Function.update_self]
    set Tnew : Finset P := (T.erase z) ∪ C.image (fun c => z * c) with hTnewdef
    have hdisj : Disjoint (T.erase z) (C.image (fun c => z * c)) := by
      rw [Finset.disjoint_left]
      intro x hx hx2
      obtain ⟨c, hc, hcx⟩ := Finset.mem_image.mp hx2
      exact hH5 x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx) c (hDc c hc)
        (by rw [hcx])
    -- the new elements pairwise fail to commute
    have hnewnc : ∀ c ∈ C, ∀ d ∈ C, c ≠ d → ¬ Commute (z * c) (z * d) := by
      intro c hc d hd hcd
      rw [commute_zmul_iff (hCz c hc) (hCz d hd)]
      intro hcomm
      exact hCcl c hc d hd hcd
        (by rw [commutatorElement_eq_one_iff_commute.mpr hcomm]; exact Subgroup.one_mem _)
    refine ⟨Tnew, z * a, an', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- the new set is noncommuting
      intro x hx y hy hxy
      simp only [hTnewdef, Finset.coe_union, Set.mem_union, Finset.coe_image,
        Finset.mem_coe, Set.mem_image] at hx hy
      rcases hx with hx | ⟨c, hc, rfl⟩
      · rcases hy with hy | ⟨d, hd, rfl⟩
        · exact hnc (Finset.mem_coe.mpr (Finset.mem_of_mem_erase hx))
            (Finset.mem_coe.mpr (Finset.mem_of_mem_erase hy)) hxy
        · exact hH5 x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx) d (hDc d hd)
      · rcases hy with hy | ⟨d, hd, rfl⟩
        · intro hcomm
          exact hH5 y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy) c (hDc c hc)
            hcomm.symm
        · exact hnewnc c hc d hd (fun h => hxy (by rw [h]))
    · -- the new distinguished element belongs to the new set
      rw [hTnewdef]
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ haC)
    · -- anchors lie in their stage subgroups
      intro j hj
      rcases Nat.lt_or_ge j m with h | h
      · rw [han'lt j h]; exact hanA j h
      · have hjm : j = m := by omega
        subst hjm
        rw [han'm]
        exact (hCmem a haC).1
    · -- anchors are annihilated by, and commute with, the earlier ones
      intro j hj j' hj'
      rcases Nat.lt_or_ge j m with h | h
      · rw [han'lt j h, han'lt j' (by omega)]
        exact hanpr j h j' hj'
      · have hjm : j = m := by omega
        subst hjm
        rw [han'm, han'lt j' hj']
        exact ⟨((hCmem a haC).2 j' hj').1, ((hCmem a haC).2 j' hj').2⟩
    · -- the new distinguished element is centralized by the constrained elements
      intro u hu
      have h1 : Commute u z := hH4 u (fun j hj => by rw [← han'lt j hj]; exact hu j (by omega))
      have h2 : Commute u a := by rw [← han'm]; exact hu m (by omega)
      exact h1.mul_right h2
    · -- the key noncommutation invariant
      intro x hx hxz u hu
      have huz : Commute u z :=
        hH4 u (fun j hj => by rw [← han'lt j hj]; exact (hu j (by omega)).2.2)
      have hua : Commute u a := by
        have := (hu m (by omega)).2.2
        rwa [han'm] at this
      rw [hTnewdef, Finset.mem_union] at hx
      rcases hx with hx | hx
      · -- a vertex from an earlier stage
        have hau : ∀ j, j < m →
            a * u ∈ Br.A (kk j) ∧ Br.pr (kk j) (a * u) = 0 ∧ Commute (a * u) (an j) := by
          intro j hj
          obtain ⟨haA, hapr, hacom⟩ := hDc a haC j hj
          obtain ⟨huA, hupr, hucom⟩ := hu j (by omega)
          rw [han'lt j hj] at hucom
          exact ⟨(Br.A (kk j)).mul_mem haA huA,
            by rw [Br.pr_mul (kk j) a haA u huA, hapr, hupr, add_zero],
            hacom.mul_left hucom⟩
        have := hH5 x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx) (a * u) hau
        rwa [← mul_assoc] at this
      · -- a vertex of the new block
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
        have hca : c ≠ a := by
          intro h
          exact hxz (by rw [h])
        have hcz : Commute c z := hCz c hc
        have haz : Commute a z := hCz a haC
        have hauz : Commute (a * u) z := haz.mul_left huz
        rw [mul_assoc, commute_zmul_iff hcz hauz]
        intro hcomm
        -- work modulo the next term of the central series
        have hcA : c ∈ Br.A (kk m) := (hCmem c hc).1
        have huA : u ∈ Br.A (kk m) := (hu m (by omega)).1
        have hupr : Br.pr (kk m) u = 0 := (hu m (by omega)).2.1
        have hcu : ⁅c, u⁆ ∈ S.K (S.L - kk m - 1) := by
          refine (Br.f_comm (kk m) hkL c hcA u huA).mp ?_
          rw [hupr, map_zero]
        have hkey : ⁅c, a * u⁆ = ⁅c, a⁆ * (a * ⁅c, u⁆ * a⁻¹) := by group
        rw [commutatorElement_eq_one_iff_commute.mpr hcomm] at hkey
        have hca' : ⁅c, a⁆ = (a * ⁅c, u⁆ * a⁻¹)⁻¹ := by
          rw [eq_inv_iff_mul_eq_one, ← hkey]
        have := S.K_normal (S.L - kk m - 1)
        refine hCcl c hc a haC hca ?_
        rw [hca']
        exact Subgroup.inv_mem _ (Subgroup.Normal.conj_mem ‹_› _ hcu a)
    · -- the cardinality estimate
      have hz1 : 1 ≤ T.card := Finset.card_pos.mpr ⟨z, hzT⟩
      have hinj : Function.Injective (fun c : P => z * c) := fun x y h => mul_left_cancel h
      have hcard : (Tnew.card : ℝ) = (T.card : ℝ) - 1 + (C.card : ℝ) := by
        rw [hTnewdef, Finset.card_union_of_disjoint hdisj,
          Finset.card_image_of_injective _ hinj, Finset.card_erase_of_mem hzT]
        rw [Nat.cast_add, Nat.cast_sub hz1, Nat.cast_one]
      have hmmR : (mm : ℝ)
          = (∑ j ∈ Finset.range m, (interRank Br (kk j) (kk m) : ℝ)) + (m : ℝ) * l := by
        rw [hmmdef]
        push_cast
        ring
      rw [Finset.sum_range_succ, hcard]
      rw [hmmR] at hCcard
      linarith [hTcard, hCcard]

end NestedAnchor

/-- Enumerating a finite set of naturals by its order embedding. -/
theorem finset_eq_image_orderEmbOfFin (E : Finset ℕ) :
    E = Finset.univ.image (E.orderEmbOfFin (rfl : E.card = E.card)) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hx
    have hr : x ∈ Set.range (E.orderEmbOfFin (rfl : E.card = E.card)) := by
      rw [Finset.range_orderEmbOfFin]; exact hx
    obtain ⟨i, hi⟩ := hr
    exact ⟨i, hi⟩
  · rintro ⟨i, rfl⟩
    exact Finset.orderEmbOfFin_mem _ _ _


/-- **Corollary 5.6** (Selected-stage composition). -/
theorem selected_stage_composition :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [Fact q.Prime] (P : Type) [Group P] [Finite P]
      (S : CentralFactorSeries q P) (Br : DescentBranch q P S) (n B l : ℕ)
      (E : Finset ℕ), E ⊆ Finset.range S.L →
      omegaG P = (n : ℕ∞) → (∀ g : P, (Subgroup.centralizer ({g} : Set P)).index ≤ B) →
      Real.logb q B ≤ (l : ℝ) →
      kappa q * (∑ k ∈ E, (Br.rho k : ℝ))
        - 2 * kappa q * (∑ k ∈ E, ∑ j ∈ E.filter (· < k), (interRank Br j k : ℝ))
        - C * (kappa q * (E.card : ℝ) ^ 2 * l + cc q * E.card) ≤ (n : ℝ) := by
  classical
  refine ⟨2, by norm_num, ?_⟩
  intro q _ P _ _ S Br n B l E hE hn hB hl
  have hq : q.Prime := Fact.out
  have hkap : (0:ℝ) ≤ kappa q := le_of_lt (kappa_pos hq.two_le)
  have hcc : (0:ℝ) ≤ cc q := by
    rw [cc]; split <;> norm_num
  have hl0 : (0:ℝ) ≤ (l : ℝ) := Nat.cast_nonneg _
  -- `B` is at most `q ^ l`
  have hB1 : 1 ≤ B := by
    have h1 := hB 1
    have h0 : 0 < (Subgroup.centralizer ({(1 : P)} : Set P)).index :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    omega
  have hBq : B ≤ q ^ l := by
    have hqR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq.one_lt
    have hBR : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB1
    have h1 : (B : ℝ) = (q : ℝ) ^ (Real.logb q B) :=
      (Real.rpow_logb (by linarith) (by linarith) hBR).symm
    have h2 : (q : ℝ) ^ (Real.logb q B) ≤ (q : ℝ) ^ (l : ℝ) :=
      Real.rpow_le_rpow_left_iff hqR |>.mpr hl
    have h3 : (B : ℝ) ≤ (q : ℝ) ^ (l : ℝ) := by rw [h1]; exact h2
    rw [Real.rpow_natCast] at h3
    exact_mod_cast h3
  -- the increasing enumeration of the selected stages
  set kk : ℕ → ℕ := fun i => if h : i < E.card then E.orderEmbOfFin rfl ⟨i, h⟩ else S.L + i
    with hkkdef
  have hkkm : ∀ (i : ℕ) (h : i < E.card), kk i = E.orderEmbOfFin rfl ⟨i, h⟩ := by
    intro i h
    rw [hkkdef]
    simp only [dite_eq_left h]
  have hkkL : ∀ i, i < E.card → kk i < S.L := by
    intro i hi
    rw [hkkm i hi]
    have h1 := hE (Finset.orderEmbOfFin_mem E rfl ⟨i, hi⟩)
    simpa using h1
  have hmono : StrictMono kk := by
    intro i j hij
    by_cases hj : j < E.card
    · have hi : i < E.card := by omega
      rw [hkkm i hi, hkkm j hj]
      exact (E.orderEmbOfFin rfl).strictMono (by simpa using hij)
    · rw [hkkdef]
      simp only [dite_eq_right hj]
      by_cases hi : i < E.card
      · rw [dite_eq_left hi]
        have h1 : kk i < S.L := hkkL i hi
        rw [hkkm i hi] at h1
        omega
      · rw [dite_eq_right hi]
        omega
  -- the noncommuting set produced by the nested construction
  obtain ⟨T, z, an, hnc, -, -, -, -, -, hTcard⟩ :=
    nested_stage_construction Br kk hmono l B hB hBq E.card hkkL
  have hTn : (T.card : ℝ) ≤ (n : ℝ) := by
    have h1 : (T.card : ℕ∞) ≤ omegaG P := card_le_omegaG T hnc
    rw [hn] at h1
    have h2 : T.card ≤ n := by exact_mod_cast h1
    exact_mod_cast h2
  -- reindexing the sums
  have hsum1 : ∀ g : ℕ → ℝ, ∑ x ∈ E, g x = ∑ i ∈ Finset.range E.card, g (kk i) := by
    intro g
    rw [← Fin.sum_univ_eq_sum_range (fun i => g (kk i)) E.card]
    conv_lhs => rw [finset_eq_image_orderEmbOfFin E]
    rw [Finset.sum_image (fun a _ b _ h => (E.orderEmbOfFin rfl).injective h)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hkkm i i.isLt]
  have hfilter : ∀ (i : ℕ), i < E.card →
      E.filter (fun x => x < kk i) = (Finset.range i).image kk := by
    intro i hi
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨hxE, hxlt⟩
      have hr : x ∈ Set.range (E.orderEmbOfFin (rfl : E.card = E.card)) := by
        rw [Finset.range_orderEmbOfFin]; exact hxE
      obtain ⟨j, rfl⟩ := hr
      refine ⟨j, ?_, by rw [hkkm (j : ℕ) j.isLt]⟩
      rw [hkkm i hi] at hxlt
      have h2 := (E.orderEmbOfFin rfl).lt_iff_lt.mp hxlt
      change (j : ℕ) < i at h2
      exact h2
    · rintro ⟨j, hj, rfl⟩
      have hjm : j < E.card := by omega
      refine ⟨?_, hmono hj⟩
      rw [hkkm j hjm]
      exact Finset.orderEmbOfFin_mem _ _ _
  have hsum2 : ∀ (i : ℕ), i < E.card → ∀ g : ℕ → ℝ,
      ∑ j ∈ E.filter (fun x => x < kk i), g j = ∑ j ∈ Finset.range i, g (kk j) := by
    intro i hi g
    rw [hfilter i hi, Finset.sum_image (fun a _ b _ h => hmono.injective h)]
  have hrho : ∑ k ∈ E, (Br.rho k : ℝ) = ∑ i ∈ Finset.range E.card, (Br.rho (kk i) : ℝ) :=
    hsum1 _
  have hinter : ∑ k ∈ E, ∑ j ∈ E.filter (· < k), (interRank Br j k : ℝ)
      = ∑ i ∈ Finset.range E.card, ∑ j ∈ Finset.range i, (interRank Br (kk j) (kk i) : ℝ) := by
    rw [hsum1 (fun k => ∑ j ∈ E.filter (· < k), (interRank Br j k : ℝ))]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    exact hsum2 i (Finset.mem_range.mp hi) _
  -- expanding the sum of stage credits
  have hexpand : ∑ i ∈ Finset.range E.card,
      (kappa q * ((Br.rho (kk i) : ℝ)
        - 2 * ((∑ j ∈ Finset.range i, (interRank Br (kk j) (kk i) : ℝ)) + i * l)) - cc q)
      = kappa q * (∑ i ∈ Finset.range E.card, (Br.rho (kk i) : ℝ))
        - 2 * kappa q * (∑ i ∈ Finset.range E.card,
            ∑ j ∈ Finset.range i, (interRank Br (kk j) (kk i) : ℝ))
        - 2 * kappa q * (∑ i ∈ Finset.range E.card, (i : ℝ) * l)
        - cc q * E.card := by
    have h1 : ∀ i ∈ Finset.range E.card,
        (kappa q * ((Br.rho (kk i) : ℝ)
          - 2 * ((∑ j ∈ Finset.range i, (interRank Br (kk j) (kk i) : ℝ)) + i * l)) - cc q)
        = kappa q * (Br.rho (kk i) : ℝ)
          - 2 * kappa q * (∑ j ∈ Finset.range i, (interRank Br (kk j) (kk i) : ℝ))
          - 2 * kappa q * ((i : ℝ) * l) - cc q := by
      intro i _
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm (E.card : ℝ) (cc q)]
  -- the arithmetic tail
  have hSl : ∑ i ∈ Finset.range E.card, (i : ℝ) * l ≤ (E.card : ℝ) ^ 2 * l := by
    calc ∑ i ∈ Finset.range E.card, (i : ℝ) * l
        ≤ ∑ _i ∈ Finset.range E.card, (E.card : ℝ) * l := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          have h1 : (i : ℝ) ≤ (E.card : ℝ) := by
            exact_mod_cast le_of_lt (Finset.mem_range.mp hi)
          exact mul_le_mul_of_nonneg_right h1 hl0
      _ = (E.card : ℝ) ^ 2 * l := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hkapSl : kappa q * (∑ i ∈ Finset.range E.card, (i : ℝ) * l)
      ≤ kappa q * ((E.card : ℝ) ^ 2 * l) := mul_le_mul_of_nonneg_left hSl hkap
  have hccm : (0:ℝ) ≤ cc q * E.card := mul_nonneg hcc (Nat.cast_nonneg _)
  rw [hexpand] at hTcard
  rw [hrho, hinter]
  linarith [hTcard, hTn, hkapSl, hccm]

/-- **Lemma 5.5** (Nested-anchor composition): the special case of Corollary 5.6 in which every
stage of the branch is selected. -/
theorem nested_anchor_composition :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [Fact q.Prime] (P : Type) [Group P] [Finite P]
      (S : CentralFactorSeries q P) (Br : DescentBranch q P S) (n B l : ℕ),
      omegaG P = (n : ℕ∞) → (∀ g : P, (Subgroup.centralizer ({g} : Set P)).index ≤ B) →
      Real.logb q B ≤ (l : ℝ) →
      kappa q * (∑ k ∈ Finset.range S.L, (Br.rho k : ℝ))
        - 2 * kappa q * (∑ k ∈ Finset.range S.L, ∑ j ∈ Finset.range k, (interRank Br j k : ℝ))
        - C * (kappa q * (S.L : ℝ) ^ 2 * l + cc q * S.L) ≤ (n : ℝ) := by
  obtain ⟨C, hC, h⟩ := selected_stage_composition
  refine ⟨C, hC, ?_⟩
  intro q _ P _ _ S Br n B l hn hB hl
  have hfil : ∀ k ∈ Finset.range S.L, (Finset.range S.L).filter (· < k) = Finset.range k := by
    intro k hk
    rw [Finset.mem_range] at hk
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
  have hkey := h q P S Br n B l (Finset.range S.L) Finset.Subset.rfl hn hB hl
  have hsum : ∀ k ∈ Finset.range S.L,
      ∑ j ∈ (Finset.range S.L).filter (· < k), (interRank Br j k : ℝ)
        = ∑ j ∈ Finset.range k, (interRank Br j k : ℝ) := fun k hk => by rw [hfil k hk]
  rw [Finset.sum_congr rfl hsum, Finset.card_range] at hkey
  exact hkey

/-- **Lemma 5.7** (Interaction product inequality).

The manuscript states the inequality only when the factor in parentheses is positive; the proof
given here shows that this proviso is unnecessary, so it has been dropped from the statement. -/
theorem interaction_product_inequality {q : ℕ} [Fact q.Prime] {P : Type} [Group P] [Finite P]
    {S : CentralFactorSeries q P} (Br : DescentBranch q P S) (n B l j k d : ℕ)
    (hn : omegaG P = (n : ℕ∞))
    (hB : ∀ g : P, (Subgroup.centralizer ({g} : Set P)).index ≤ B)
    (hl : Real.logb q B ≤ (l : ℝ)) (hj : j < S.L) (hk : k < S.L) (hjk : j < k)
    (hd : 1 ≤ d) (hdt : d ≤ interRank Br j k) :
    ((d : ℝ) + 1) * (kappa q * ((Br.rho k : ℝ) - 2 * (d + 1) * l) - cc q + 1) ≤ (n : ℝ) := by
  classical
  have hq : q.Prime := Fact.out
  have : NeZero q := ⟨hq.ne_zero⟩
  -- `B` bounds an index, hence is at least one, and is at most `q ^ l`
  have hB1 : 1 ≤ B := by
    have h1 := hB 1
    have h0 : 0 < (Subgroup.centralizer ({(1 : P)} : Set P)).index :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    omega
  have hBq : B ≤ q ^ l := by
    have hqR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq.one_lt
    have hBR : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB1
    have h1 : (B : ℝ) = (q : ℝ) ^ (Real.logb q B) :=
      (Real.rpow_logb (by linarith) (by linarith) hBR).symm
    have h2 : (q : ℝ) ^ (Real.logb q B) ≤ (q : ℝ) ^ (l : ℝ) :=
      Real.rpow_le_rpow_left_iff hqR |>.mpr hl
    have h3 : (B : ℝ) ≤ (q : ℝ) ^ (l : ℝ) := by rw [h1]; exact h2
    rw [Real.rpow_natCast] at h3
    exact_mod_cast h3
  -- the transversal clique of Lemma 5.4
  obtain ⟨a, haA, hacos, hacomm⟩ := transversal_interaction_clique Br j k d hj hjk hd hdt
  set X : Subgroup P := ⨅ i : Fin (d + 1), Subgroup.centralizer ({a i} : Set P) with hX
  set Hs : Subgroup P := Br.A k ⊓ X with hHs
  have hHsA : Hs ≤ Br.A k := inf_le_left
  -- exact centralization: the elements of `Hs` commute with every member of the transversal
  have hgcent : ∀ x ∈ Hs, ∀ i : Fin (d + 1), a i * x = x * a i := by
    intro x hx i
    have h1 : x ∈ X := hx.2
    have h2 : x ∈ Subgroup.centralizer ({a i} : Set P) := (Subgroup.mem_iInf.mp h1) i
    exact Subgroup.mem_centralizer_iff.mp h2 (a i) rfl
  set m : ℕ := (d + 1) * l with hm
  -- the index of `Hs` in `A_k`
  have hrel : Hs.relIndex (Br.A k) ≤ q ^ m := by
    have h1 : Hs.relIndex (Br.A k) = X.relIndex (Br.A k) := Subgroup.inf_relIndex_left _ _
    have h2 : X.relIndex (Br.A k)
        ≤ ∏ i : Fin (d + 1), (Subgroup.centralizer ({a i} : Set P)).relIndex (Br.A k) :=
      Subgroup.relIndex_iInf_le _
    have h3 : ∀ i : Fin (d + 1),
        (Subgroup.centralizer ({a i} : Set P)).relIndex (Br.A k) ≤ B := by
      intro i
      have hne : (Subgroup.centralizer ({a i} : Set P)).relIndex ⊤ ≠ 0 := by
        rw [Subgroup.relIndex_top_right]
        exact Subgroup.index_ne_zero_of_finite
      have h4 := Subgroup.relIndex_le_of_le_right (le_top : Br.A k ≤ ⊤) hne
      rw [Subgroup.relIndex_top_right] at h4
      exact le_trans h4 (hB _)
    have h5 : (∏ i : Fin (d + 1), (Subgroup.centralizer ({a i} : Set P)).relIndex (Br.A k))
        ≤ ∏ _i : Fin (d + 1), B := Finset.prod_le_prod' (fun i _ => h3 i)
    have h6 : (∏ _i : Fin (d + 1), B) = B ^ (d + 1) := by
      simp [Finset.prod_const]
    have h7 : B ^ (d + 1) ≤ (q ^ l) ^ (d + 1) := Nat.pow_le_pow_left hBq _
    have h8 : (q ^ l) ^ (d + 1) = q ^ m := by
      rw [← pow_mul, Nat.mul_comm, hm]
    calc Hs.relIndex (Br.A k) = X.relIndex (Br.A k) := h1
      _ ≤ ∏ i : Fin (d + 1), (Subgroup.centralizer ({a i} : Set P)).relIndex (Br.A k) := h2
      _ ≤ ∏ _i : Fin (d + 1), B := h5
      _ = B ^ (d + 1) := h6
      _ ≤ (q ^ l) ^ (d + 1) := h7
      _ = q ^ m := h8
  obtain ⟨W, hWmem, hWcodim⟩ := stage_image_codim Br k hk Hs hHsA m hrel
  -- the rank of the restricted form
  have hrank : Br.rho k ≤ formRank (formRestrict (Br.f k) W) + 2 * m := by
    have h1 := formRank_restrict_ge (Br.f k) W
    rw [formRank_stage Br k hk] at h1
    omega
  obtain ⟨C, hC, hcard⟩ :=
    scalar_clique_credit (formRestrict (Br.f k) W) (formRestrict_isAlt (Br.f_alt k) W)
  choose g hgH hgpr using fun w : {x // x ∈ W} => (hWmem (w : Fin (Br.rho k) → ZMod q)).mp w.2
  -- the product set `T · D` is a noncommuting set
  set T : Finset P := (Finset.univ ×ˢ C).image (fun z : Fin (d + 1) × {x // x ∈ W} =>
    a z.1 * g z.2) with hT
  have hginj : ∀ w w' : {x // x ∈ W}, g w = g w' → w = w' := by
    intro w w' h
    have := hgpr w
    rw [h, hgpr w'] at this
    exact Subtype.ext this.symm
  have hinj : Function.Injective (fun z : Fin (d + 1) × {x // x ∈ W} => a z.1 * g z.2) := by
    rintro ⟨i, w⟩ ⟨i', w'⟩ h
    by_cases hii : i = i'
    · subst hii
      have hgg : g w = g w' := mul_left_cancel h
      exact Prod.ext rfl (hginj w w' hgg)
    · exfalso
      have hmem : (a i)⁻¹ * a i' ∈ Br.A k := by
        have he : (a i)⁻¹ * a i' = g w * (g w')⁻¹ := by
          have hbeta : a i * g w = a i' * g w' := h
          have h2 : (a i)⁻¹ * (a i * g w) = (a i)⁻¹ * (a i' * g w') := by rw [hbeta]
          rw [← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul] at h2
          rw [h2]
          group
        rw [he]
        exact hHsA (Hs.mul_mem (hgH w) (Hs.inv_mem (hgH w')))
      exact hacos i i' hii hmem
  have hTcard : T.card = (d + 1) * C.card := by
    rw [hT, Finset.card_image_of_injective _ hinj, Finset.card_product, Finset.card_univ,
      Fintype.card_fin]
  have hnc : IsNoncommSet (T : Set P) := by
    intro x hx y hy hxy
    simp only [hT, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product,
      Finset.mem_univ, true_and] at hx hy
    obtain ⟨⟨i, w⟩, hwC, rfl⟩ := hx
    obtain ⟨⟨i', w'⟩, hw'C, rfl⟩ := hy
    have hgwk : g w ∈ Br.A k := hHsA (hgH w)
    have hgw'k : g w' ∈ Br.A k := hHsA (hgH w')
    by_cases hii : i = i'
    · subst hii
      have hww' : w ≠ w' := by
        intro h
        exact hxy (by rw [h])
      have hphi : (Br.f k) (Br.pr k (g w)) (Br.pr k (g w')) ≠ 0 := by
        have h1 := hC w (Finset.mem_coe.mpr hwC) w' (Finset.mem_coe.mpr hw'C) hww'
        rw [hgpr w, hgpr w']
        simpa [formRestrict] using h1
      have hcomm : ⁅g w, g w'⁆ ∉ S.K (S.L - k - 1) := fun hmem =>
        hphi ((Br.f_comm k hk (g w) hgwk (g w') hgw'k).mpr hmem)
      have hne1 : ⁅g w, g w'⁆ ≠ 1 := fun h => hcomm (by rw [h]; exact Subgroup.one_mem _)
      have hnotcomm : ¬ Commute (g w) (g w') := fun hc =>
        hne1 (commutatorElement_eq_one_iff_commute.mpr hc)
      intro hc
      apply hnotcomm
      have hcw := hgcent (g w) (hgH w) i
      have e1 : a i * g w * (a i * g w') = a i * a i * (g w * g w') := by
        calc a i * g w * (a i * g w') = a i * (g w * a i) * g w' := by group
          _ = a i * (a i * g w) * g w' := by rw [← hcw]
          _ = a i * a i * (g w * g w') := by group
      have hcw' := hgcent (g w') (hgH w') i
      have e2 : a i * g w' * (a i * g w) = a i * a i * (g w' * g w) := by
        calc a i * g w' * (a i * g w) = a i * (g w' * a i) * g w := by group
          _ = a i * (a i * g w') * g w := by rw [← hcw']
          _ = a i * a i * (g w' * g w) := by group
      have h3 : a i * a i * (g w * g w') = a i * a i * (g w' * g w) := by
        rw [← e1, ← e2]
        exact hc
      exact mul_left_cancel h3
    · intro hc
      -- the commutator of the two anchors survives, whereas the `Hs`-part is absorbed
      have hggN : ⁅g w', g w⁆ ∈ S.K (S.L - j - 1) := by
        have h1 : ⁅g w', g w⁆ ∈ S.K (S.L - k) :=
          Br.A_der k (le_of_lt hk) (Subgroup.commutator_mem_commutator hgw'k hgwk)
        exact centralFactorSeries_K_mono S (by omega) h1
      have hcw := hgcent (g w) (hgH w) i'
      have hcw' := hgcent (g w') (hgH w') i
      have e1 : a i * g w * (a i' * g w') = a i * a i' * (g w * g w') := by
        calc a i * g w * (a i' * g w') = a i * (g w * a i') * g w' := by group
          _ = a i * (a i' * g w) * g w' := by rw [← hcw]
          _ = a i * a i' * (g w * g w') := by group
      have e2 : a i' * g w' * (a i * g w) = a i' * a i * (g w' * g w) := by
        calc a i' * g w' * (a i * g w) = a i' * (g w' * a i) * g w := by group
          _ = a i' * (a i * g w') * g w := by rw [← hcw']
          _ = a i' * a i * (g w' * g w) := by group
      have hkey : a i * a i' * (g w * g w') = a i' * a i * (g w' * g w) := by
        rw [← e1, ← e2]; exact hc
      have hsplit : a i * a i' = a i' * a i * (g w' * g w) * (g w * g w')⁻¹ := by
        rw [← hkey]; group
      have hmain : ⁅a i, a i'⁆ = (a i' * a i) * ⁅g w', g w⁆ * (a i' * a i)⁻¹ := by
        rw [commutatorElement_def, hsplit, commutatorElement_def]
        group
      have hnormal : (S.K (S.L - j - 1)).Normal := S.K_normal _
      have hmem : ⁅a i, a i'⁆ ∈ S.K (S.L - j - 1) := by
        rw [hmain]
        exact hnormal.conj_mem _ hggN _
      exact hacomm i i' hii hmem
  -- counting
  have hcardle : (T.card : ℕ∞) ≤ omegaG P := card_le_omegaG T hnc
  rw [hn] at hcardle
  have hTn : T.card ≤ n := by exact_mod_cast hcardle
  have hCn : ((d : ℝ) + 1) * (C.card : ℝ) ≤ (n : ℝ) := by
    have h1 : (d + 1) * C.card ≤ n := by rw [← hTcard]; exact hTn
    have h2 : (((d + 1) * C.card : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith
  have hkap : 0 ≤ kappa q := le_of_lt (kappa_pos hq.two_le)
  have hrankR : (Br.rho k : ℝ) - 2 * ((d : ℝ) + 1) * l
      ≤ (formRank (formRestrict (Br.f k) W) : ℝ) := by
    have h1 : ((Br.rho k : ℕ) : ℝ)
        ≤ ((formRank (formRestrict (Br.f k) W) : ℕ) : ℝ) + ((2 * m : ℕ) : ℝ) := by
      exact_mod_cast hrank
    rw [hm] at h1
    push_cast at h1
    linarith
  have hX1 : kappa q * ((Br.rho k : ℝ) - 2 * ((d : ℝ) + 1) * l) - cc q + 1 ≤ (C.card : ℝ) := by
    nlinarith [hcard, hkap, hrankR]
  have hd0 : (0 : ℝ) ≤ (d : ℝ) + 1 := by positivity
  calc ((d : ℝ) + 1) * (kappa q * ((Br.rho k : ℝ) - 2 * (d + 1) * l) - cc q + 1)
      ≤ ((d : ℝ) + 1) * (C.card : ℝ) := by
        exact mul_le_mul_of_nonneg_left hX1 hd0
    _ ≤ (n : ℝ) := hCn

/-- A pairwise nonorthogonal set in the stage-`j` symplectic space lifts to a noncommuting set
of the same size in `P`. -/
theorem stage_nonorth_card_le {q : ℕ} [Fact q.Prime] {P : Type} [Group P] [Finite P]
    {S : CentralFactorSeries q P} (Br : DescentBranch q P S) (j : ℕ) (hj : j < S.L)
    (C : Finset (Fin (Br.rho j) → ZMod q))
    (hC : IsNonorthSet (Br.f j) (C : Set (Fin (Br.rho j) → ZMod q))) :
    (C.card : ℕ∞) ≤ omegaG P := by
  classical
  choose a haA hapr using fun v : (Fin (Br.rho j) → ZMod q) => Br.pr_surj j hj v
  have hainj : Function.Injective a := by
    intro v v' h
    rw [← hapr v, ← hapr v', h]
  have hnc : IsNoncommSet ((C.image a : Finset P) : Set P) := by
    intro x hx y hy hxy
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
    obtain ⟨v, hv, rfl⟩ := hx
    obtain ⟨v', hv', rfl⟩ := hy
    have hvv' : v ≠ v' := fun h => hxy (by rw [h])
    have hne : Br.f j v v' ≠ 0 := hC v hv v' hv' hvv'
    intro hcomm
    have h1 : ⁅a v, a v'⁆ = 1 := commutatorElement_eq_one_iff_commute.mpr hcomm
    have h2 : Br.f j (Br.pr j (a v)) (Br.pr j (a v')) = 0 :=
      (Br.f_comm j hj (a v) (haA v) (a v') (haA v')).mpr (by rw [h1]; exact Subgroup.one_mem _)
    rw [hapr v, hapr v'] at h2
    exact hne h2
  have := card_le_omegaG (C.image a) hnc
  rwa [Finset.card_image_of_injective _ hainj] at this

/-- The scalar clique credit of the full stage-`k` form, read in `P`. -/
theorem stage_rank_credit {q : ℕ} [Fact q.Prime] {P : Type} [Group P] [Finite P]
    {S : CentralFactorSeries q P} (Br : DescentBranch q P S) (k n : ℕ) (hk : k < S.L)
    (hn : omegaG P = (n : ℕ∞)) :
    kappa q * (Br.rho k : ℝ) - cc q + 1 ≤ (n : ℝ) := by
  obtain ⟨C, hC, hcard⟩ := scalar_clique_credit (Br.f k) (Br.f_alt k)
  have h1 : (C.card : ℕ∞) ≤ (n : ℕ∞) := by
    rw [← hn]; exact stage_nonorth_card_le Br k hk C hC
  have h2 : C.card ≤ n := by exact_mod_cast h1
  have h3 : (C.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2
  rw [formRank_stage Br k hk] at hcard
  linarith

/-- Uniformly in the prime, `ω(P)` is at least `(3/4)·κ_q·ρ_k` at any stage of rank at least 2. -/
theorem stage_rank_three_quarters {q : ℕ} [Fact q.Prime] {P : Type} [Group P] [Finite P]
    {S : CentralFactorSeries q P} (Br : DescentBranch q P S) (k n : ℕ) (hk : k < S.L)
    (hrho : 2 ≤ Br.rho k) (hn : omegaG P = (n : ℕ∞)) :
    (3 / 4 : ℝ) * (kappa q * (Br.rho k : ℝ)) ≤ (n : ℝ) := by
  have hcred := stage_rank_credit Br k n hk hn
  have hprime : q.Prime := Fact.out
  have hr2 : (2 : ℝ) ≤ (Br.rho k : ℝ) := by exact_mod_cast hrho
  rcases eq_or_ne q 2 with rfl | h2
  · simp only [kappa, cc] at hcred ⊢
    norm_num at hcred ⊢
    linarith
  rcases eq_or_ne q 3 with rfl | h3
  · simp only [kappa, cc] at hcred ⊢
    norm_num at hcred ⊢
    linarith
  · simp only [kappa, cc, ite_eq_right h2, ite_eq_right h3] at hcred ⊢
    have hq5 : (5 : ℝ) ≤ (q : ℝ) := by
      have := hprime.two_le
      have h4 : q ≠ 4 := by rintro rfl; norm_num at hprime
      have : 5 ≤ q := by omega
      exact_mod_cast this
    nlinarith


/-- A uniform slack estimate for the constant `c_q` of the scalar clique credit. -/
theorem cc_sub_one_le (q : ℕ) [Fact q.Prime] {r : ℝ} (hr : 2 ≤ r) :
    cc q - 1 ≤ (8 / 15) * (kappa q * r) := by
  have hprime : q.Prime := Fact.out
  rcases eq_or_ne q 2 with rfl | h2
  · simp only [kappa, cc]; norm_num; linarith
  rcases eq_or_ne q 3 with rfl | h3
  · simp only [kappa, cc]; norm_num; linarith
  · have hq5 : (5 : ℝ) ≤ (q : ℝ) := by
      have := hprime.two_le
      have h4 : q ≠ 4 := by rintro rfl; norm_num at hprime
      have : 5 ≤ q := by omega
      exact_mod_cast this
    simp only [kappa, cc, ite_eq_right h2, ite_eq_right h3]
    nlinarith

/-- **Corollary 5.8** (Expensive stages have small interaction). -/
theorem expensive_stage_small_interaction :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧ ∀ (q : ℕ) [Fact q.Prime] (P : Type) [Group P] [Finite P]
      (S : CentralFactorSeries q P) (Br : DescentBranch q P S) (n B l j k : ℕ),
      omegaG P = (n : ℕ∞) → (∀ g : P, (Subgroup.centralizer ({g} : Set P)).index ≤ B) →
      Real.logb q B ≤ (l : ℝ) → j < k → k < S.L → j < S.L → 2 ≤ Br.rho k →
      C₀ * (n : ℝ) * l ≤ kappa q * (Br.rho k : ℝ) ^ 2 →
      (interRank Br j k : ℝ) ≤ C₁ * (n : ℝ) / (kappa q * (Br.rho k : ℝ)) := by
  refine ⟨100, 6, by norm_num, by norm_num, ?_⟩
  intro q _ P _ _ S Br n B l j k hn hB hl hjk hk hj hrho hC0
  have hprime : q.Prime := Fact.out
  set K : ℝ := kappa q with hK
  set R : ℝ := (Br.rho k : ℝ) with hR
  set N : ℝ := (n : ℝ) with hN
  set L : ℝ := (l : ℝ) with hL
  have hk0 : 0 < K := kappa_pos hprime.two_le
  have hr2 : (2 : ℝ) ≤ R := by rw [hR]; exact_mod_cast hrho
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have h34 : (3 / 4 : ℝ) * (K * R) ≤ N := stage_rank_three_quarters Br k n hk hrho hn
  have hkr : 0 < K * R := by nlinarith
  have hN0 : 0 < N := by nlinarith
  set x : ℝ := 4 * N / (K * R) with hx
  have hxkr : x * (K * R) = 4 * N := by
    rw [hx, div_mul_cancel₀ _ (ne_of_gt hkr)]
  have hx3 : (3 : ℝ) ≤ x := by
    rw [hx, le_div_iff₀ hkr]
    linarith
  set d : ℕ := ⌈x⌉₊ with hd
  have hdge : x ≤ (d : ℝ) := Nat.le_ceil x
  have hdlt : (d : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
  by_cases hdt : d ≤ interRank Br j k
  · exfalso
    have hd1 : 1 ≤ d := by
      have : (1 : ℝ) ≤ (d : ℝ) := by linarith
      exact_mod_cast this
    -- the interaction term is small
    have hxL : x * L ≤ R / 25 := by
      have h1 : (x * L) * (K * R) ≤ (R / 25) * (K * R) := by nlinarith [hC0, hL0, hxkr]
      exact le_of_mul_le_mul_right h1 hkr
    have hsmall : 2 * ((d : ℝ) + 1) * L ≤ (2 / 15) * R := by
      have h2 : (d : ℝ) + 1 ≤ (5 / 3) * x := by linarith
      nlinarith [hL0, hxL, hx3]
    have hterm : K * R / 3 ≤ K * (R - 2 * ((d : ℝ) + 1) * L) - cc q + 1 := by
      have h1 : K * (R - 2 * ((d : ℝ) + 1) * L) ≥ (13 / 15) * (K * R) := by nlinarith [hk0, hsmall]
      have h2 := cc_sub_one_le q hr2
      rw [← hK] at h2
      linarith
    have h57 := interaction_product_inequality Br n B l j k d hn hB hl hj hk hjk hd1 hdt
    have hfin : ((d : ℝ) + 1) * (K * R / 3) ≤ N := by
      refine le_trans ?_ h57
      have hd1' : (0 : ℝ) < (d : ℝ) + 1 := by positivity
      exact mul_le_mul_of_nonneg_left hterm (le_of_lt hd1')
    nlinarith [hfin, hdge, hxkr, hN0]
  · push Not at hdt
    have hlt : ((interRank Br j k : ℕ) : ℝ) < x := Nat.lt_ceil.mp hdt
    rw [le_div_iff₀ hkr]
    nlinarith [hlt, hxkr, hN0, hkr]


/-! ## 6. The `p`-group upper bound -/

/-- Every group carries a pairwise noncommuting set of size one, so `ω(G) ≥ 1`. -/
theorem one_le_omegaG {G : Type*} [Group G] : (1 : ℕ∞) ≤ omegaG G := by
  classical
  have h : IsNoncommSet ((({1} : Finset G)) : Set G) := by
    intro x hx y hy hxy
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx hy
    exact absurd (hx.trans hy.symm) hxy
  have h2 := card_le_omegaG ({1} : Finset G) h
  simpa using h2

/-- Along a central factor series the `i`-th term has order `q^i`. -/
theorem centralFactorSeries_K_card {q : ℕ} [Fact q.Prime] {P : Type} [Group P] [Finite P]
    (S : CentralFactorSeries q P) : ∀ i, i ≤ S.L → Nat.card (S.K i) = q ^ i := by
  intro i
  induction i with
  | zero => intro _; rw [S.K_zero]; simp
  | succ i ih =>
    intro h
    rw [S.K_card i (by omega), ih (by omega), pow_succ]
    ring

/-- The length of a central factor series is `log_q |P'|`. -/
theorem centralFactorSeries_card_commutator {q : ℕ} [Fact q.Prime] {P : Type} [Group P]
    [Finite P] (S : CentralFactorSeries q P) : Nat.card (commutator P) = q ^ S.L := by
  rw [← S.K_top]
  exact centralFactorSeries_K_card S S.L le_rfl

/-- A uniform comparison of `(log₂ (n+2))²` with `√n`. -/
theorem logb_two_sq_le_sqrt (n : ℕ) (hn : 1 ≤ n) :
    (Real.logb 2 ((n : ℝ) + 2)) ^ 2 ≤ 100 * Real.sqrt n := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set t : ℝ := (n : ℝ) + 2 with ht
  have ht0 : (0 : ℝ) < t := by rw [ht]; linarith
  have hq : Real.log (t ^ ((1:ℝ)/4)) = (1/4) * Real.log t := Real.log_rpow ht0 _
  have hle : Real.log (t ^ ((1:ℝ)/4)) ≤ t ^ ((1:ℝ)/4) - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ht0 _)
  have hlog : Real.log t ≤ 4 * t ^ ((1:ℝ)/4) := by
    rw [hq] at hle; linarith
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlogpos : (0:ℝ) < Real.log 2 := by linarith
  have hrppos : (0:ℝ) < t ^ ((1:ℝ)/4) := Real.rpow_pos_of_pos ht0 _
  have hlb : Real.logb 2 t ≤ 4 * t ^ ((1:ℝ)/4) / 0.6931471803 := by
    rw [Real.logb, div_le_iff₀ hlogpos]
    have hnn : (0:ℝ) ≤ 4 * t ^ ((1:ℝ)/4) / 0.6931471803 := by positivity
    calc Real.log t ≤ 4 * t ^ ((1:ℝ)/4) := hlog
      _ = 4 * t ^ ((1:ℝ)/4) / 0.6931471803 * 0.6931471803 := by ring
      _ ≤ 4 * t ^ ((1:ℝ)/4) / 0.6931471803 * Real.log 2 := by nlinarith
  have hlbnn : 0 ≤ Real.logb 2 t := by
    rw [Real.logb]
    have : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
    positivity
  have hsq : (Real.logb 2 t) ^ 2 ≤ (4 * t ^ ((1:ℝ)/4) / 0.6931471803) ^ 2 :=
    pow_le_pow_left₀ hlbnn hlb 2
  have hrp : (t ^ ((1:ℝ)/4)) ^ 2 = Real.sqrt t := by
    rw [← Real.rpow_natCast (t ^ ((1:ℝ)/4)) 2, ← Real.rpow_mul ht0.le, Real.sqrt_eq_rpow]
    norm_num
  have hsq2 : (4 * t ^ ((1:ℝ)/4) / 0.6931471803) ^ 2
      = (16 / 0.6931471803 ^ 2) * Real.sqrt t := by
    rw [div_pow, mul_pow, hrp]; ring
  have hst : Real.sqrt t ≤ Real.sqrt 3 * Real.sqrt n := by
    rw [← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    rw [ht]; linarith
  have hs3 : Real.sqrt 3 ≤ 1.8 := by
    rw [show (1.8:ℝ) = Real.sqrt (1.8^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hsn : 0 ≤ Real.sqrt (n:ℝ) := Real.sqrt_nonneg _
  have hst2 : Real.sqrt t ≤ 1.8 * Real.sqrt n := le_trans hst (by nlinarith)
  calc (Real.logb 2 t) ^ 2 ≤ (16 / 0.6931471803 ^ 2) * Real.sqrt t := by rw [← hsq2]; exact hsq
    _ ≤ (16 / 0.6931471803 ^ 2) * (1.8 * Real.sqrt n) := by
        have hc : (0:ℝ) ≤ 16 / 0.6931471803 ^ 2 := by norm_num
        exact mul_le_mul_of_nonneg_left hst2 hc
    _ ≤ 100 * Real.sqrt n := by nlinarith [hsn]

/-- `log₂ (n+2) ≤ 1.45 · log (n+2)`. -/
theorem logb_le_log (x : ℝ) (hx : 0 ≤ Real.log x) : Real.logb 2 x ≤ 1.45 * Real.log x := by
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  rw [Real.logb, div_le_iff₀ (by linarith)]
  nlinarith

/-- Arithmetic core of the proof of Proposition 6.2: once the combinatorial estimates have been
assembled, the remaining inequality is a purely numerical statement about real parameters. -/
theorem two_group_final_arith
    (C₁ C₂ C₅ A D K L X s Lam R u l : ℝ)
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hC₅ : 0 < C₅)
    (hA1 : 1 ≤ A)
    (hKdef : K = (C₁ / A) * D ^ 3 + (A / 2) * D ^ 3 + 300 * C₅ * C₂ ^ 2 + 200 * C₂)
    (hs1 : 1 ≤ s) (hLam1 : 1 ≤ Lam) (hl0 : 0 ≤ l) (hL0 : 0 ≤ L)
    (hXdef : X = C₁ * s / (A * u)) (hRdef : R = A * s * u)
    (hu1 : 1 ≤ u) (husq : u ^ 2 = L + l) (huD : u ≤ D * Lam)
    (hLle : L ≤ C₂ * Lam ^ 2) (hlLam : l ≤ 6 * Lam) (hLamsq : Lam ^ 2 ≤ 100 * s) :
    L * (L * X) + (C₅ / 2) * (L ^ 2 * l) + L * (R + 2) / 2 + L ≤ K * s * Lam ^ 3 := by
  have hA0 : (0:ℝ) < A := by linarith
  have hu0 : (0:ℝ) < u := by linarith
  have hs0 : (0:ℝ) < s := by linarith
  have hLam0 : (0:ℝ) < Lam := by linarith
  have hX0 : 0 ≤ X := by
    rw [hXdef]
    exact div_nonneg (mul_nonneg hC₁.le hs0.le) (mul_nonneg hA0.le hu0.le)
  have hLu : L ≤ u ^ 2 := by rw [husq]; linarith
  have huLam : u ^ 3 ≤ D ^ 3 * Lam ^ 3 := by
    have h1 : u ^ 3 ≤ (D * Lam) ^ 3 := pow_le_pow_left₀ (le_of_lt hu0) huD 3
    rw [mul_pow] at h1; exact h1
  -- the interaction term
  have ht1 : L * (L * X) ≤ (C₁ / A) * D ^ 3 * Lam ^ 3 * s := by
    have hb : (0:ℝ) ≤ u ^ 2 * X := mul_nonneg (sq_nonneg u) hX0
    have ha : L * X ≤ u ^ 2 * X := mul_le_mul_of_nonneg_right hLu hX0
    have h1 : L * (L * X) ≤ u ^ 2 * (u ^ 2 * X) :=
      le_trans (mul_le_mul_of_nonneg_left ha hL0) (mul_le_mul_of_nonneg_right hLu hb)
    have h2 : u ^ 2 * (u ^ 2 * X) = (C₁ / A) * u ^ 3 * s := by
      rw [hXdef]; field_simp
    have hca : (0:ℝ) ≤ C₁ / A := le_of_lt (div_pos hC₁ hA0)
    have h3 : (C₁ / A) * u ^ 3 * s ≤ (C₁ / A) * (D ^ 3 * Lam ^ 3) * s :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left huLam hca) hs0.le
    calc L * (L * X) ≤ u ^ 2 * (u ^ 2 * X) := h1
      _ = (C₁ / A) * u ^ 3 * s := h2
      _ ≤ (C₁ / A) * (D ^ 3 * Lam ^ 3) * s := h3
      _ = (C₁ / A) * D ^ 3 * Lam ^ 3 * s := by ring
  -- the error term of Corollary 5.6
  have ht2 : (C₅ / 2) * (L ^ 2 * l) ≤ 300 * C₅ * C₂ ^ 2 * s * Lam ^ 3 := by
    have h1 : L ^ 2 ≤ (C₂ * Lam ^ 2) ^ 2 := by nlinarith
    have h2 : L ^ 2 * l ≤ (C₂ * Lam ^ 2) ^ 2 * (6 * Lam) :=
      le_trans (mul_le_mul_of_nonneg_right h1 hl0)
        (mul_le_mul_of_nonneg_left hlLam (sq_nonneg _))
    have hc : (0:ℝ) ≤ 6 * C₂ ^ 2 * Lam ^ 3 :=
      mul_nonneg (by positivity) (pow_nonneg hLam0.le 3)
    have h5 := mul_le_mul_of_nonneg_left hLamsq hc
    have h7 := mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ C₅ / 2)
    have h8 := mul_le_mul_of_nonneg_left h5 (by linarith : (0:ℝ) ≤ C₅ / 2)
    linarith
  -- the cheap stages
  have ht3 : L * (R + 2) / 2 ≤ (A / 2) * D ^ 3 * Lam ^ 3 * s + L := by
    have h1 : L * R ≤ u ^ 2 * (A * s * u) := by
      rw [hRdef]
      exact mul_le_mul_of_nonneg_right hLu (mul_nonneg (mul_nonneg hA0.le hs0.le) hu0.le)
    have heq : u ^ 2 * (A * s * u) = A * u ^ 3 * s := by ring
    have h3 : A * u ^ 3 * s ≤ A * (D ^ 3 * Lam ^ 3) * s :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left huLam hA0.le) hs0.le
    rw [heq] at h1
    linarith
  -- the number of stages
  have ht4 : 2 * L ≤ 200 * C₂ * s * Lam ^ 3 := by
    have h1 : C₂ * Lam ^ 2 ≤ C₂ * (100 * s) := mul_le_mul_of_nonneg_left hLamsq hC₂.le
    have h2 : (1:ℝ) ≤ Lam ^ 3 := one_le_pow₀ hLam1
    have h3 : (0:ℝ) ≤ 200 * C₂ * s := mul_nonneg (by linarith) hs0.le
    have h4 := mul_le_mul_of_nonneg_left h2 h3
    linarith
  rw [hKdef]
  linarith



/-- `κ_q ≥ 1` for every prime `q`. -/
theorem one_le_kappa {q : ℕ} (hq : 2 ≤ q) : 1 ≤ kappa q := by
  unfold kappa
  split_ifs with h2 h3
  · exact le_rfl
  · norm_num
  · have h4 : (4 : ℝ) ≤ (q : ℝ) := by
      have h4' : 4 ≤ q := by omega
      exact_mod_cast h4'
    linarith

/-- `c_q ≥ 0` for every prime `q`. -/
theorem cc_nonneg (q : ℕ) : 0 ≤ cc q := by
  unfold cc; split_ifs <;> norm_num

/-- `c_q ≤ 2` for every prime `q`. -/
theorem cc_le_two (q : ℕ) : cc q ≤ 2 := by
  unfold cc; split_ifs <;> norm_num

/-- A uniform comparison of `(log (n+2))⁴` with `√n`. -/
theorem log_pow_four_le_sqrt (n : ℕ) (hn : 1 ≤ n) :
    (Real.log ((n : ℝ) + 2)) ^ 4 ≤ 7373 * Real.sqrt n := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set t : ℝ := (n : ℝ) + 2 with ht
  have ht0 : (0 : ℝ) < t := by rw [ht]; linarith
  have hq : Real.log (t ^ ((1:ℝ)/8)) = (1/8) * Real.log t := Real.log_rpow ht0 _
  have hle : Real.log (t ^ ((1:ℝ)/8)) ≤ t ^ ((1:ℝ)/8) - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ht0 _)
  have hlog : Real.log t ≤ 8 * t ^ ((1:ℝ)/8) := by
    rw [hq] at hle; linarith
  have hrppos : (0:ℝ) < t ^ ((1:ℝ)/8) := Real.rpow_pos_of_pos ht0 _
  have hlogpos : 0 ≤ Real.log t := Real.log_nonneg (by rw [ht]; linarith)
  have hsq : (Real.log t) ^ 4 ≤ (8 * t ^ ((1:ℝ)/8)) ^ 4 := pow_le_pow_left₀ hlogpos hlog 4
  have hrp : (t ^ ((1:ℝ)/8)) ^ 4 = Real.sqrt t := by
    rw [← Real.rpow_natCast (t ^ ((1:ℝ)/8)) 4, ← Real.rpow_mul ht0.le, Real.sqrt_eq_rpow]
    norm_num
  have hsq2 : (8 * t ^ ((1:ℝ)/8)) ^ 4 = 4096 * Real.sqrt t := by
    rw [mul_pow, hrp]; norm_num
  have hst : Real.sqrt t ≤ Real.sqrt 3 * Real.sqrt n := by
    rw [← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    rw [ht]; linarith
  have hs3 : Real.sqrt 3 ≤ 1.8 := by
    rw [show (1.8:ℝ) = Real.sqrt (1.8^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; norm_num
  have hsn : 0 ≤ Real.sqrt (n:ℝ) := Real.sqrt_nonneg _
  have hst2 : Real.sqrt t ≤ 1.8 * Real.sqrt n := le_trans hst (by nlinarith)
  calc (Real.log t) ^ 4 ≤ 4096 * Real.sqrt t := by rw [← hsq2]; exact hsq
    _ ≤ 4096 * (1.8 * Real.sqrt n) := by linarith
    _ ≤ 7373 * Real.sqrt n := by linarith

set_option maxHeartbeats 4000000 in
/-- **Proposition 6.2**, uniform version.  For every prime `q`, every finite `q`-group `P` and
`n = ω(P)`,
`log₂ a(P) ≤ α_q n + C √n (log (n+2))³`,
with an absolute constant `C`.  For `q = 2` this is Proposition 6.2 of the manuscript, and for
general `q` it is the quantitative form of Theorem 6.1.

The Neumann–Vaughan-Lee bound (via Corollary 3.2, which controls the length of the central factor
series) enters as an explicit hypothesis. -/
theorem pgroup_sqrt_bound (hNVL : NeumannVaughanLeeBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [Fact q.Prime] (P : Type) [Group P] [Finite P] (n : ℕ),
      IsPGroup q P → omegaG P = (n : ℕ∞) →
      log2a P ≤ alphaP q * n + C * Real.sqrt n * (Real.log (n + 2)) ^ 3 := by
  classical
  obtain ⟨C₅, hC₅, h56⟩ := selected_stage_composition
  obtain ⟨C₀, C₁, hC₀, hC₁, h58⟩ := expensive_stage_small_interaction
  obtain ⟨C₂, hC₂, h32⟩ := log2_card_commutator_le hNVL
  set A : ℝ := C₀ + 1 with hAdef
  have hA1 : 1 ≤ A := by rw [hAdef]; linarith
  have hA0 : 0 < A := by linarith
  have hA2 : C₀ ≤ A ^ 2 := by nlinarith [sq_nonneg (A - 1)]
  set D : ℝ := Real.sqrt (C₂ + 6) with hDdef
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hDsq : D ^ 2 = C₂ + 6 := Real.sq_sqrt (by linarith)
  set K : ℝ := (C₁ / A) * D ^ 3 + (A / 2) * D ^ 3 + 300 * C₅ * C₂ ^ 2 + 200 * C₂ with hKdef
  have hK0 : 0 < K := by
    have h1 : 0 ≤ (C₁ / A) * D ^ 3 := by positivity
    have h2 : 0 ≤ (A / 2) * D ^ 3 := by positivity
    have h3 : 0 ≤ 300 * C₅ * C₂ ^ 2 := by positivity
    have h4 : 0 < 200 * C₂ := by linarith
    linarith
  refine ⟨4 * (K + C₅ * C₂), by positivity, ?_⟩
  intro q _ P _ _ n hP hn
  have hq : q.Prime := Fact.out
  have hq2 : 2 ≤ q := hq.two_le
  have hq2R : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hkap1 : 1 ≤ kappa q := one_le_kappa hq2
  have hkap0 : (0 : ℝ) < kappa q := by linarith
  -- basic numerical quantities
  have hn1 : 1 ≤ n := by
    have h1 : (1 : ℕ∞) ≤ omegaG P := one_le_omegaG
    rw [hn] at h1
    exact_mod_cast h1
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  set s : ℝ := Real.sqrt n with hsdef
  have hs1 : 1 ≤ s := by
    rw [hsdef, show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hnR
  have hs0 : 0 < s := by linarith
  have hssq : s ^ 2 = (n : ℝ) := Real.sq_sqrt (by linarith)
  set lam : ℝ := Real.log ((n : ℝ) + 2) with hlamdef
  have hlam0 : 0 ≤ lam := Real.log_nonneg (by linarith)
  set Lam : ℝ := Real.logb 2 ((n : ℝ) + 2) with hLamdef
  have hLam1 : 1 ≤ Lam := by
    rw [hLamdef, show (1:ℝ) = Real.logb 2 2 by simp]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by linarith)
  have hLam0 : 0 ≤ Lam := by linarith
  have hLamlam : Lam ≤ 1.45 * lam := logb_le_log _ hlam0
  have hLamcube : Lam ^ 3 ≤ 4 * lam ^ 3 := by
    have h1 : Lam ^ 3 ≤ (1.45 * lam) ^ 3 := pow_le_pow_left₀ hLam0 hLamlam 3
    nlinarith [pow_nonneg hlam0 3]
  have hLamsq : Lam ^ 2 ≤ 100 * s := logb_two_sq_le_sqrt n hn1
  have halph0 : 0 ≤ alphaP q := by
    rw [alphaP]
    apply div_nonneg _ (by linarith)
    exact Real.logb_nonneg (by norm_num) (by linarith)
  -- the central factor series and a branch of the cover tree
  obtain ⟨S⟩ := exists_centralFactorSeries q P hP
  obtain ⟨Br, hbr⟩ := branch_cover_bound hP S
  set gam : ℝ := Real.logb 2 (q : ℝ) with hgamdef
  have hgam1 : 1 ≤ gam := by
    rw [hgamdef, show (1:ℝ) = Real.logb 2 2 by simp]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) hq2R
  have hgam0 : 0 ≤ gam := by linarith
  rcases Nat.eq_zero_or_pos S.L with hL0 | hLpos
  · rw [hL0] at hbr
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, mul_zero, add_zero] at hbr
    have h1 : 0 ≤ 4 * (K + C₅ * C₂) * s * lam ^ 3 := by positivity
    have h2 : 0 ≤ alphaP q * n := mul_nonneg halph0 (by positivity)
    linarith
  -- the bound `B` on centraliser indices and its logarithm `l`
  set B : ℕ := (2 * n + 1) ^ 2 with hBdef
  have hBidx : ∀ g : P, (Subgroup.centralizer ({g} : Set P)).index ≤ B :=
    fun g => conjClass_index_le n (le_of_eq hn) g
  set l : ℕ := ⌈2 * (1 + Lam)⌉₊ with hldef
  have hlB : Real.logb 2 B ≤ (l : ℝ) := by
    have hcast : ((B : ℕ) : ℝ) = (2 * (n:ℝ) + 1) ^ 2 := by rw [hBdef]; push_cast; ring
    have h1 : Real.logb 2 ((2 * (n:ℝ) + 1) ^ 2) = 2 * Real.logb 2 (2 * (n:ℝ) + 1) := by
      rw [Real.logb_pow]
      norm_num
    have h2 : Real.logb 2 (2 * (n:ℝ) + 1) ≤ Real.logb 2 (2 * ((n:ℝ) + 2)) :=
      Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
    have h3 : Real.logb 2 (2 * ((n:ℝ) + 2)) = 1 + Lam := by
      rw [Real.logb_mul (by norm_num) (by linarith), hLamdef]
      norm_num
    have h4 : (2 : ℝ) * (1 + Lam) ≤ (l : ℝ) := by
      rw [hldef]
      exact Nat.le_ceil _
    rw [h3] at h2
    rw [hcast, h1]
    linarith
  have hB1 : 1 ≤ B := by
    rw [hBdef]
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hlBq : Real.logb q B ≤ (l : ℝ) := by
    refine le_trans ?_ hlB
    rw [Real.logb, Real.logb]
    have hlogB : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast hB1)
    have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlogq : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hq2R
    exact div_le_div_of_nonneg_left hlogB hlog2 hlogq
  have hlLam : (l : ℝ) ≤ 6 * Lam := by
    have h1 : (l : ℝ) < 2 * (1 + Lam) + 1 := by
      rw [hldef]
      exact Nat.ceil_lt_add_one (by linarith)
    linarith
  have hl0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg _
  -- the length of the series, weighted by `log₂ q`
  set ell : ℝ := (S.L : ℝ) with helldef
  have hell1 : (1 : ℝ) ≤ ell := by rw [helldef]; exact_mod_cast hLpos
  have hell0 : (0 : ℝ) ≤ ell := by linarith
  set Lp : ℝ := gam * ell with hLpdef
  have hLple : Lp ≤ C₂ * Lam ^ 2 := by
    have h1 := h32 P n (le_of_eq hn)
    rw [centralFactorSeries_card_commutator S] at h1
    have h2 : ((q ^ S.L : ℕ) : ℝ) = (q : ℝ) ^ S.L := by push_cast; ring
    rw [h2, Real.logb_pow] at h1
    rw [hLpdef, helldef, hgamdef, mul_comm]
    exact h1
  have hLp1 : (1 : ℝ) ≤ Lp := by
    rw [hLpdef]; nlinarith
  have hLp0 : (0 : ℝ) ≤ Lp := by linarith
  have hellLp : ell ≤ Lp := by rw [hLpdef]; nlinarith
  -- the threshold
  set u : ℝ := Real.sqrt (Lp + (l : ℝ)) with hudef
  have hu1 : 1 ≤ u := by
    rw [hudef, show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have hu0 : 0 < u := by linarith
  have husq : u ^ 2 = Lp + (l : ℝ) := Real.sq_sqrt (by linarith)
  have huD : u ≤ D * Lam := by
    have h1 : Lp + (l : ℝ) ≤ (D * Lam) ^ 2 := by
      have h2 : (D * Lam) ^ 2 = (C₂ + 6) * Lam ^ 2 := by rw [mul_pow, hDsq]
      nlinarith [hLple, hlLam, hLam1]
    calc u = Real.sqrt (Lp + (l : ℝ)) := hudef
      _ ≤ Real.sqrt ((D * Lam) ^ 2) := Real.sqrt_le_sqrt h1
      _ = D * Lam := Real.sqrt_sq (by positivity)
  set R : ℝ := A * s * u with hRdef
  have hR0 : 0 < R := by rw [hRdef]; positivity
  set E : Finset ℕ := (Finset.range S.L).filter (fun k => R + 2 ≤ (Br.rho k : ℝ)) with hEdef
  have hEsub : E ⊆ Finset.range S.L := Finset.filter_subset _ _
  have hEcard : (E.card : ℝ) ≤ ell := by
    have h1 := Finset.card_le_card hEsub
    rw [Finset.card_range] at h1
    rw [helldef]
    exact_mod_cast h1
  have hEcard0 : (0 : ℝ) ≤ (E.card : ℝ) := Nat.cast_nonneg _
  -- interaction bound on the selected stages
  set X : ℝ := C₁ * s / (A * u) with hXdef
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  have hinter : ∀ k ∈ E, ∀ j ∈ E.filter (· < k), (interRank Br j k : ℝ) ≤ X := by
    intro k hk j hj
    rw [hEdef, Finset.mem_filter, Finset.mem_range] at hk
    have hjk : j < k := (Finset.mem_filter.mp hj).2
    have hjE := (Finset.mem_filter.mp hj).1
    rw [hEdef, Finset.mem_filter, Finset.mem_range] at hjE
    have hrho2 : 2 ≤ Br.rho k := by
      have h1 : (2 : ℝ) ≤ (Br.rho k : ℝ) := le_trans (by linarith) hk.2
      exact_mod_cast h1
    have hrhoR : R ≤ (Br.rho k : ℝ) := by linarith [hk.2]
    have hexp : C₀ * (n : ℝ) * l ≤ kappa q * (Br.rho k : ℝ) ^ 2 := by
      have h1 : R ^ 2 ≤ (Br.rho k : ℝ) ^ 2 := pow_le_pow_left₀ hR0.le hrhoR 2
      have h2 : R ^ 2 = A ^ 2 * (n : ℝ) * (Lp + (l : ℝ)) := by
        rw [hRdef, mul_pow, mul_pow, hssq, husq]
      have h3 : C₀ * (n : ℝ) * l ≤ A ^ 2 * (n : ℝ) * (Lp + (l : ℝ)) := by
        have hn0 : (0:ℝ) ≤ (n:ℝ) := by linarith
        have hstep1 : C₀ * (n : ℝ) * (l : ℝ) ≤ A ^ 2 * (n : ℝ) * (l : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA2 hn0) hl0
        have hstep2 : A ^ 2 * (n : ℝ) * (l : ℝ) ≤ A ^ 2 * (n : ℝ) * (Lp + (l : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        linarith
      have h4 : (Br.rho k : ℝ) ^ 2 ≤ kappa q * (Br.rho k : ℝ) ^ 2 :=
        le_mul_of_one_le_left (sq_nonneg _) hkap1
      linarith
    have h58' := h58 q P S Br n B l j k hn hBidx hlBq hjk hk.1 hjE.1 hrho2 hexp
    refine le_trans h58' ?_
    have hkr : R ≤ kappa q * (Br.rho k : ℝ) :=
      le_trans hrhoR (le_mul_of_one_le_left (by positivity) hkap1)
    have hstep : C₁ * (n : ℝ) / (kappa q * (Br.rho k : ℝ)) ≤ C₁ * (n : ℝ) / R :=
      div_le_div_of_nonneg_left (by positivity) hR0 hkr
    refine le_trans hstep (le_of_eq ?_)
    rw [hXdef, hRdef, ← hssq]
    field_simp
  -- Corollary 5.6 on the selected stages
  have h56' := h56 q P S Br n B l E hEsub hn hBidx hlBq
  have hdouble : ∑ k ∈ E, ∑ j ∈ E.filter (· < k), (interRank Br j k : ℝ)
      ≤ ell * (ell * X) := by
    have hstep : ∀ k ∈ E, ∑ j ∈ E.filter (· < k), (interRank Br j k : ℝ) ≤ ell * X := by
      intro k hk
      calc ∑ j ∈ E.filter (· < k), (interRank Br j k : ℝ)
          ≤ ∑ _j ∈ E.filter (· < k), X := Finset.sum_le_sum (fun j hj => hinter k hk j hj)
        _ = ((E.filter (· < k)).card : ℝ) * X := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ell * X := by
            have h1 : ((E.filter (· < k)).card : ℝ) ≤ ell := by
              refine le_trans ?_ hEcard
              exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
            exact mul_le_mul_of_nonneg_right h1 hX0
    calc ∑ k ∈ E, ∑ j ∈ E.filter (· < k), (interRank Br j k : ℝ)
        ≤ ∑ _k ∈ E, (ell * X) := Finset.sum_le_sum hstep
      _ = (E.card : ℝ) * (ell * X) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ell * (ell * X) := by
          have h1 : (0:ℝ) ≤ ell * X := by positivity
          exact mul_le_mul_of_nonneg_right hEcard h1
  set V : ℝ := 2 * (ell * (ell * X)) + C₅ * (ell ^ 2 * (l : ℝ)) + 2 * C₅ * ell with hVdef
  have hV0 : 0 ≤ V := by rw [hVdef]; positivity
  have hexpensive : ∑ k ∈ E, (Br.rho k : ℝ) ≤ (n : ℝ) / kappa q + V := by
    have h1 : 2 * kappa q * (∑ k ∈ E, ∑ j ∈ E.filter (· < k), (interRank Br j k : ℝ))
        ≤ kappa q * (2 * (ell * (ell * X))) := by
      calc 2 * kappa q * (∑ k ∈ E, ∑ j ∈ E.filter (· < k), (interRank Br j k : ℝ))
          ≤ 2 * kappa q * (ell * (ell * X)) :=
            mul_le_mul_of_nonneg_left hdouble (by positivity)
        _ = kappa q * (2 * (ell * (ell * X))) := by ring
    have h2 : C₅ * (kappa q * (E.card : ℝ) ^ 2 * (l : ℝ))
        ≤ kappa q * (C₅ * (ell ^ 2 * (l : ℝ))) := by
      have hc2 : ((E.card : ℝ)) ^ 2 * (l : ℝ) ≤ ell ^ 2 * (l : ℝ) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hEcard0 hEcard 2) hl0
      calc C₅ * (kappa q * (E.card : ℝ) ^ 2 * (l : ℝ))
          = (C₅ * kappa q) * ((E.card : ℝ) ^ 2 * (l : ℝ)) := by ring
        _ ≤ (C₅ * kappa q) * (ell ^ 2 * (l : ℝ)) :=
            mul_le_mul_of_nonneg_left hc2 (by positivity)
        _ = kappa q * (C₅ * (ell ^ 2 * (l : ℝ))) := by ring
    have h3 : C₅ * (cc q * (E.card : ℝ)) ≤ kappa q * (2 * C₅ * ell) := by
      have ha : cc q * (E.card : ℝ) ≤ 2 * ell :=
        mul_le_mul (cc_le_two q) hEcard hEcard0 (by norm_num)
      calc C₅ * (cc q * (E.card : ℝ)) ≤ C₅ * (2 * ell) :=
            mul_le_mul_of_nonneg_left ha hC₅.le
        _ = 1 * (2 * C₅ * ell) := by ring
        _ ≤ kappa q * (2 * C₅ * ell) :=
            mul_le_mul_of_nonneg_right hkap1 (by positivity)
    have hmul : kappa q * (∑ k ∈ E, (Br.rho k : ℝ)) ≤ (n : ℝ) + kappa q * V := by
      rw [hVdef]
      linarith [h56', h1, h2, h3]
    have hle : (∑ k ∈ E, (Br.rho k : ℝ)) ≤ ((n : ℝ) + kappa q * V) / kappa q := by
      rw [le_div_iff₀ hkap0]
      linarith [hmul]
    refine le_trans hle (le_of_eq ?_)
    rw [add_div, mul_div_cancel_left₀ _ (ne_of_gt hkap0)]
  -- the cheap stages
  have hcheap : ∑ k ∈ (Finset.range S.L).filter (fun k => ¬ (R + 2 ≤ (Br.rho k : ℝ))),
      (Br.rho k : ℝ) ≤ ell * (R + 2) := by
    calc ∑ k ∈ (Finset.range S.L).filter (fun k => ¬ (R + 2 ≤ (Br.rho k : ℝ))), (Br.rho k : ℝ)
        ≤ ∑ _k ∈ (Finset.range S.L).filter (fun k => ¬ (R + 2 ≤ (Br.rho k : ℝ))), (R + 2) :=
          Finset.sum_le_sum (fun k hk => le_of_lt (not_le.mp (Finset.mem_filter.mp hk).2))
      _ = (((Finset.range S.L).filter
            (fun k => ¬ (R + 2 ≤ (Br.rho k : ℝ)))).card : ℝ) * (R + 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ell * (R + 2) := by
          have h1 : (((Finset.range S.L).filter
              (fun k => ¬ (R + 2 ≤ (Br.rho k : ℝ)))).card : ℝ) ≤ ell := by
            have h2 := Finset.card_le_card (Finset.filter_subset
              (fun k => ¬ (R + 2 ≤ (Br.rho k : ℝ))) (Finset.range S.L))
            rw [Finset.card_range] at h2
            rw [helldef]
            exact_mod_cast h2
          have h2 : (0:ℝ) ≤ R + 2 := by linarith
          exact mul_le_mul_of_nonneg_right h1 h2
  have htotal : ∑ k ∈ Finset.range S.L, (Br.rho k : ℝ)
      ≤ (n : ℝ) / kappa q + (V + ell * (R + 2)) := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range S.L)
      (fun k => R + 2 ≤ (Br.rho k : ℝ)) (fun k => (Br.rho k : ℝ))
    rw [← hEdef] at hsplit
    linarith [hexpensive, hcheap, hsplit]
  -- assembling the estimate
  have hkey : log2a P ≤ alphaP q * n
      + (Lp * (Lp * X) + (C₅ / 2) * (Lp ^ 2 * (l : ℝ)) + Lp * (R + 2) / 2 + Lp + C₅ * Lp) := by
    have hmul : gam / 2 * (∑ k ∈ Finset.range S.L, (Br.rho k : ℝ))
        ≤ gam / 2 * ((n : ℝ) / kappa q + (V + ell * (R + 2))) :=
      mul_le_mul_of_nonneg_left htotal (by positivity)
    have halph : gam / 2 * ((n : ℝ) / kappa q) = alphaP q * n := by
      rw [alphaP, ← hgamdef]
      field_simp
    have hexpand : gam / 2 * (V + ell * (R + 2))
        = Lp * (ell * X) + (C₅ / 2) * (Lp * ell * (l : ℝ)) + C₅ * Lp + Lp * (R + 2) / 2 := by
      rw [hVdef, hLpdef]; ring
    have e1 : Lp * (ell * X) ≤ Lp * (Lp * X) := by
      have h1 : ell * X ≤ Lp * X := mul_le_mul_of_nonneg_right hellLp hX0
      exact mul_le_mul_of_nonneg_left h1 hLp0
    have e2 : (C₅ / 2) * (Lp * ell * (l : ℝ)) ≤ (C₅ / 2) * (Lp ^ 2 * (l : ℝ)) := by
      have h1 : Lp * ell * (l : ℝ) ≤ Lp ^ 2 * (l : ℝ) := by
        calc Lp * ell * (l : ℝ) ≤ (Lp * Lp) * (l : ℝ) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hellLp hLp0) hl0
          _ = Lp ^ 2 * (l : ℝ) := by ring
      exact mul_le_mul_of_nonneg_left h1 (by linarith)
    have hd : gam / 2 * ((n : ℝ) / kappa q + (V + ell * (R + 2)))
        = alphaP q * n + (gam / 2 * (V + ell * (R + 2))) := by
      rw [← halph]; ring
    rw [hd, hexpand] at hmul
    linarith [hbr, hmul, e1, e2, hellLp]
  refine le_trans hkey ?_
  have hgoal : Lp * (Lp * X) + (C₅ / 2) * (Lp ^ 2 * (l : ℝ)) + Lp * (R + 2) / 2 + Lp
      ≤ K * s * Lam ^ 3 :=
    two_group_final_arith C₁ C₂ C₅ A D K Lp X s Lam R u (l : ℝ) hC₁ hC₂ hC₅ hA1 hKdef
      hs1 hLam1 hl0 hLp0 hXdef hRdef hu1 husq huD hLple hlLam hLamsq
  have hextra : C₅ * Lp ≤ C₅ * C₂ * s * Lam ^ 3 := by
    have hL23 : Lam ^ 2 ≤ Lam ^ 3 := by
      calc Lam ^ 2 = Lam ^ 2 * 1 := by ring
        _ ≤ Lam ^ 2 * Lam := mul_le_mul_of_nonneg_left hLam1 (sq_nonneg Lam)
        _ = Lam ^ 3 := by ring
    have hL2 : Lam ^ 2 ≤ s * Lam ^ 3 :=
      le_trans hL23 (le_mul_of_one_le_left (by positivity) hs1)
    calc C₅ * Lp ≤ C₅ * (C₂ * Lam ^ 2) := mul_le_mul_of_nonneg_left hLple hC₅.le
      _ ≤ C₅ * (C₂ * (s * Lam ^ 3)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL2 hC₂.le) hC₅.le
      _ = C₅ * C₂ * s * Lam ^ 3 := by ring
  have hfinal : (K + C₅ * C₂) * s * Lam ^ 3 ≤ 4 * (K + C₅ * C₂) * s * lam ^ 3 := by
    have h1 : (0:ℝ) ≤ (K + C₅ * C₂) * s := by positivity
    calc (K + C₅ * C₂) * s * Lam ^ 3 ≤ (K + C₅ * C₂) * s * (4 * lam ^ 3) :=
          mul_le_mul_of_nonneg_left hLamcube h1
      _ = 4 * (K + C₅ * C₂) * s * lam ^ 3 := by ring
  linarith [hgoal, hextra, hfinal]


/-- **Proposition 6.2** (Quantitative 2-group bound):
`log₂ a(P) ≤ n/2 + O(√n (log (n+2))³)`.

This is the case `q = 2` of `pgroup_sqrt_bound`, where `α₂ = 1/2`. -/
theorem two_group_upper_bound (hNVL : NeumannVaughanLeeBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Type) [Group P] [Finite P] (n : ℕ),
      IsPGroup 2 P → omegaG P = (n : ℕ∞) →
      log2a P ≤ (n : ℝ) / 2 + C * Real.sqrt n * (Real.log (n + 2)) ^ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨C, hC, h⟩ := pgroup_sqrt_bound hNVL
  refine ⟨C, hC, fun P _ _ n hP hn => ?_⟩
  have h1 := h 2 P n hP hn
  rwa [alphaP_two, show (1:ℝ) / 2 * (n : ℝ) = (n : ℝ) / 2 by ring] at h1

/-- **Theorem 6.1** (Uniform `p`-group bound): `log₂ a(P) ≤ α_p n + O(n / log (n+2))`,
uniformly in the prime `p`.

The nonabelianity hypothesis of the manuscript is retained, although the proof given here does
not need it.  The Neumann–Vaughan-Lee bound enters as an explicit hypothesis, as in Corollary 3.2. -/
theorem pgroup_upper_bound (hNVL : NeumannVaughanLeeBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [Fact q.Prime] (P : Type) [Group P] [Finite P] (n : ℕ),
      IsPGroup q P → (¬ ∀ x y : P, Commute x y) → omegaG P = (n : ℕ∞) →
      log2a P ≤ alphaP q * n + C * (n : ℝ) / Real.log (n + 2) := by
  obtain ⟨C, hC, h⟩ := pgroup_sqrt_bound hNVL
  refine ⟨7373 * C, by linarith, ?_⟩
  intro q _ P _ _ n hP _ hn
  have hb := h q P n hP hn
  have hn1 : 1 ≤ n := by
    have h1 : (1 : ℕ∞) ≤ omegaG P := one_le_omegaG
    rw [hn] at h1
    exact_mod_cast h1
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hlam0 : (0 : ℝ) < Real.log ((n : ℝ) + 2) := Real.log_pos (by linarith)
  have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
    Real.mul_self_sqrt (by linarith)
  have h4 := log_pow_four_le_sqrt n hn1
  have hs0 : (0 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hkey : C * Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3
      ≤ 7373 * C * (n : ℝ) / Real.log ((n : ℝ) + 2) := by
    rw [le_div_iff₀ hlam0]
    have h5 : Real.sqrt (n : ℝ) * (Real.log ((n : ℝ) + 2)) ^ 4
        ≤ Real.sqrt (n : ℝ) * (7373 * Real.sqrt (n : ℝ)) :=
      mul_le_mul_of_nonneg_left h4 hs0
    nlinarith [hC.le, h5, hsq]
  linarith [hb, hkey]

open Filter Topology in
/-- Auxiliary: `(log x)³ / √x → 0` as `x → ∞` over the reals. -/
theorem log_cube_div_sqrt_atTop_real :
    Tendsto (fun x : ℝ => Real.log x ^ 3 / Real.sqrt x) atTop (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => Real.log y ^ 3 / (1 * y + 0)) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 3 one_ne_zero
  have h2 := (h1.comp Real.tendsto_sqrt_atTop).const_mul (8 : ℝ)
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  have hs : Real.sqrt x > 0 := Real.sqrt_pos.mpr hx
  simp only [Function.comp_apply, one_mul, add_zero, Real.log_sqrt hx.le]
  field_simp
  ring

open Filter Topology in
/-- Auxiliary: the error term of the main theorem is `o(n)`, i.e.
`(log (n+2))³ / √n → 0`. -/
theorem log_cube_div_sqrt_tendsto :
    Tendsto (fun n : ℕ => (Real.log (n + 2)) ^ 3 / Real.sqrt n) atTop (𝓝 0) := by
  have hb : Tendsto (fun n : ℕ => (2:ℝ) * (Real.log (n+2) ^ 3 / Real.sqrt (n+2)))
      atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    have := (log_cube_div_sqrt_atTop_real.comp h).const_mul (2:ℝ)
    simpa using this
  refine squeeze_zero' ?_ ?_ hb
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hlog : 0 ≤ Real.log ((n:ℝ)+2) := Real.log_nonneg (by linarith)
    have : (0:ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
    positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hs : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
    have hs2 : (0:ℝ) < Real.sqrt ((n:ℝ)+2) := Real.sqrt_pos.mpr (by linarith)
    have hle : Real.sqrt ((n:ℝ)+2) ≤ 2 * Real.sqrt n := by
      rw [show (2:ℝ) * Real.sqrt n = Real.sqrt (4 * n) by
        rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
          rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]]
      apply Real.sqrt_le_sqrt; linarith
    have hlog : 0 ≤ Real.log ((n:ℝ)+2) := Real.log_nonneg (by linarith)
    have hL : (0:ℝ) ≤ Real.log ((n:ℝ)+2) ^ 3 := pow_nonneg hlog 3
    rw [div_le_iff₀ hs, show (2:ℝ) * (Real.log ((n:ℝ)+2) ^ 3 / Real.sqrt ((n:ℝ)+2))
        * Real.sqrt n
      = 2 * Real.log ((n:ℝ)+2) ^ 3 * Real.sqrt n / Real.sqrt ((n:ℝ)+2) by ring,
      le_div_iff₀ hs2]
    nlinarith

/-! ## 7. Nilpotent groups

The passage from `p`-groups to nilpotent groups uses the decomposition of a finite nilpotent
group as the direct product of its Sylow subgroups.  Abelian covering numbers are submultiplicative
and pairwise noncommuting sets are supermultiplicative along direct products, and the mismatch is
favourable. -/

/-! ### General facts about `a(G)` -/
/-- A finite group has a finite abelian cover, so `a(G) ≠ ⊤`. -/
theorem aG_ne_top {G : Type} [Group G] [Finite G] : aG G ≠ ⊤ := by
  have := Fintype.ofFinite G
  have h : aG G ≤ ((Finset.univ.image (fun x : G => Subgroup.zpowers x)).card : ℕ∞) := by
    refine iInf_le (fun C : {C : Finset (Subgroup G) // IsAbelianCover C} =>
      ((C : Finset (Subgroup G)).card : ℕ∞)) ⟨_, ?_, ?_⟩
    · intro A hA
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hA
      intro u hu v hv
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      exact zpow_mul_comm x m k
    · intro g
      exact ⟨Subgroup.zpowers g, Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩,
        Subgroup.mem_zpowers g⟩
  intro htop
  rw [htop] at h
  exact (not_le.mpr (ENat.natCast_lt_top _)) h

/-- If `a(G) ≤ k` then `G` has an abelian cover by at most `k` subgroups. -/
theorem exists_cover_of_aG_le {G : Type} [Group G] (k : ℕ) (h : aG G ≤ (k : ℕ∞)) :
    ∃ C : Finset (Subgroup G), (∀ A ∈ C, ∀ x ∈ A, ∀ y ∈ A, Commute x y) ∧
      (∀ g : G, ∃ A ∈ C, g ∈ A) ∧ C.card ≤ k := by
  by_contra hcon
  push Not at hcon
  have hle : ((k : ℕ) + 1 : ℕ∞) ≤ aG G := by
    refine le_iInf ?_
    rintro ⟨C, hC1, hC2⟩
    have h1 : k < C.card := hcon C hC1 hC2
    have h2 : k + 1 ≤ C.card := by omega
    exact_mod_cast h2
  have h2 : ((k + 1 : ℕ) : ℕ∞) ≤ ((k : ℕ) : ℕ∞) := by exact_mod_cast le_trans hle h
  have := (Nat.cast_le (α := ℕ∞)).mp h2
  omega

/-- A finite group is never covered by an empty family of abelian subgroups. -/
theorem one_le_aG_toNat {G : Type} [Group G] [Finite G] : 1 ≤ (aG G).toNat := by
  rcases Nat.eq_zero_or_pos (aG G).toNat with h0 | h
  · exfalso
    have hle : aG G ≤ ((0:ℕ) : ℕ∞) := by
      have hco : ((aG G).toNat : ℕ∞) = aG G := ENat.natCast_toNat aG_ne_top
      rw [← hco, h0]
    obtain ⟨C, -, hCcov, hCcard⟩ := exists_cover_of_aG_le 0 hle
    have hCe : C = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hCcard)
    obtain ⟨A, hA, -⟩ := hCcov 1
    rw [hCe] at hA
    exact absurd hA (Finset.notMem_empty _)
  · exact h
/-! ### Isomorphism invariance of the two parameters -/

/-- `ω` does not increase along an isomorphism. -/
theorem omegaG_le_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    omegaG G ≤ omegaG H := by
  classical
  refine iSup_le ?_
  rintro ⟨S, hS⟩
  have hnc : IsNoncommSet ((S.image (e : G → H) : Finset H) : Set H) := by
    intro x hx y hy hxy hcomm
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have hab : a ≠ b := fun h => hxy (by rw [h])
    refine hS ha hb hab ?_
    have h1 : e (a * b) = e (b * a) := by
      rw [map_mul, map_mul]; exact hcomm
    exact e.injective h1
  have h2 := card_le_omegaG (S.image (e : G → H)) hnc
  rwa [Finset.card_image_of_injective _ e.injective] at h2

/-- `ω` is an isomorphism invariant. -/
theorem omegaG_eq_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    omegaG G = omegaG H :=
  le_antisymm (omegaG_le_of_mulEquiv e) (omegaG_le_of_mulEquiv e.symm)

/-- An abelian cover transports along an isomorphism. -/
theorem aG_le_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H) : aG H ≤ aG G := by
  classical
  refine le_iInf ?_
  rintro ⟨C, hC1, hC2⟩
  have hcov : IsAbelianCover (C.image (fun A => A.map (e : G →* H))) := by
    constructor
    · intro B hB
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
      intro x hx y hy
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
      exact (hC1 A hA a ha b hb).map (e : G →* H)
    · intro g
      obtain ⟨A, hA, hg⟩ := hC2 (e.symm g)
      refine ⟨A.map (e : G →* H), Finset.mem_image_of_mem _ hA, ?_⟩
      have h1 : e (e.symm g) ∈ A.map (e : G →* H) := Subgroup.mem_map_of_mem _ hg
      simpa using h1
  refine le_trans (aG_le_of_cover _ hcov) ?_
  exact_mod_cast Finset.card_image_le

/-- `a` is an isomorphism invariant. -/
theorem aG_eq_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H) : aG G = aG H :=
  le_antisymm (aG_le_of_mulEquiv e.symm) (aG_le_of_mulEquiv e)

/-- `log₂ a` is an isomorphism invariant. -/
theorem log2a_eq_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    log2a G = log2a H := by
  unfold log2a
  rw [aG_eq_of_mulEquiv e]

/-! ### Elementary properties of `ω` and `a` -/

/-- A finite group has a finite `ω`. -/
theorem omegaG_ne_top {G : Type} [Group G] [Finite G] : omegaG G ≠ ⊤ := by
  classical
  have := Fintype.ofFinite G
  intro htop
  have h : omegaG G ≤ ((Fintype.card G : ℕ) : ℕ∞) := by
    rw [omegaG_le_iff]
    intro S _
    simpa using Finset.card_le_univ S
  rw [htop] at h
  exact (not_le.mpr (ENat.natCast_lt_top _)) h

/-- `log₂ a(G) ≥ 0`. -/
theorem log2a_nonneg {G : Type} [Group G] [Finite G] : 0 ≤ log2a G := by
  unfold log2a
  exact Real.logb_nonneg (by norm_num) (by exact_mod_cast one_le_aG_toNat)

/-- An abelian group is covered by one abelian subgroup, so `log₂ a(G) = 0`. -/
theorem log2a_eq_zero_of_abelian {G : Type} [Group G] [Finite G]
    (h : ∀ x y : G, Commute x y) : log2a G = 0 := by
  classical
  have hcov : IsAbelianCover ({⊤} : Finset (Subgroup G)) := by
    constructor
    · intro A hA
      rw [Finset.mem_singleton] at hA
      subst hA
      intro x _ y _
      exact h x y
    · intro g
      exact ⟨⊤, Finset.mem_singleton_self _, Subgroup.mem_top g⟩
  have hle : aG G ≤ ((1 : ℕ) : ℕ∞) := by simpa using aG_le_of_cover _ hcov
  have h1 : (aG G).toNat ≤ 1 := by
    have h2 := ENat.toNat_le_toNat hle (ENat.natCast_ne_top 1)
    simpa using h2
  have h2 : (aG G).toNat = 1 := le_antisymm h1 one_le_aG_toNat
  unfold log2a
  rw [h2]
  simp

/-- A nonabelian group has a pairwise noncommuting set of size three. -/
theorem three_le_omegaG_of_nonabelian {G : Type} [Group G]
    (h : ¬ ∀ x y : G, Commute x y) : (3 : ℕ∞) ≤ omegaG G := by
  classical
  push Not at h
  obtain ⟨x, y, hxy⟩ := h
  have hx1 : x ≠ 1 := by rintro rfl; exact hxy (Commute.one_left y)
  have hy1 : y ≠ 1 := by rintro rfl; exact hxy (Commute.one_right x)
  have hne1 : x ≠ y := by rintro rfl; exact hxy (Commute.refl x)
  have hne2 : x ≠ x * y := by
    intro hEq
    refine hy1 ?_
    have h1 : x * 1 = x * y := by rwa [mul_one]
    exact (mul_left_cancel h1).symm
  have hne3 : y ≠ x * y := by
    intro hEq
    refine hx1 ?_
    have h1 : 1 * y = x * y := by rwa [one_mul]
    exact (mul_right_cancel h1).symm
  have hnc1 : ¬ Commute x (x * y) := by
    intro hc
    refine hxy ?_
    have h1 : x * (x * y) = (x * y) * x := hc
    rw [mul_assoc] at h1
    exact mul_left_cancel h1
  have hnc2 : ¬ Commute y (x * y) := by
    intro hc
    refine hxy ?_
    have h1 : y * (x * y) = (x * y) * y := hc
    rw [← mul_assoc] at h1
    exact (mul_right_cancel h1).symm
  have hS : IsNoncommSet (({x, y, x * y} : Finset G) : Set G) := by
    intro a ha b hb hab
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hab
        | exact hxy
        | exact fun hc => hxy hc.symm
        | exact hnc1
        | exact fun hc => hnc1 hc.symm
        | exact hnc2
        | exact fun hc => hnc2 hc.symm
  have hcard : ({x, y, x * y} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hne1, hne2]),
      Finset.card_insert_of_notMem (by simp [hne3]), Finset.card_singleton]
  have h1 := card_le_omegaG _ hS
  rw [hcard] at h1
  exact_mod_cast h1

/-- If `k ≤ ω(G)` then some pairwise noncommuting set has at least `k` elements. -/
theorem exists_noncomm_card_ge {G : Type} [Group G] (k : ℕ) (h : (k : ℕ∞) ≤ omegaG G) :
    ∃ S : Finset G, IsNoncommSet (S : Set G) ∧ k ≤ S.card := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨∅, ?_, by simp⟩
    intro x hx
    simp at hx
  by_contra hcon
  push Not at hcon
  have hle : omegaG G ≤ ((k - 1 : ℕ) : ℕ∞) := by
    rw [omegaG_le_iff]
    intro S hS
    have h1 := hcon S hS
    omega
  have h2 : (k : ℕ∞) ≤ ((k - 1 : ℕ) : ℕ∞) := le_trans h hle
  have h3 : k ≤ k - 1 := by exact_mod_cast h2
  omega

/-! ### Direct products -/

/-- Cartesian products of pairwise noncommuting sets are pairwise noncommuting. -/
theorem omegaG_pi_ge {ι : Type} [Fintype ι] (G : ι → Type) [∀ i, Group (G i)] (m : ι → ℕ)
    (hm : ∀ i, (m i : ℕ∞) ≤ omegaG (G i)) :
    ((∏ i, m i : ℕ) : ℕ∞) ≤ omegaG (∀ i, G i) := by
  classical
  choose S hS hcard using fun i => exists_noncomm_card_ge (m i) (hm i)
  have hnc : IsNoncommSet ((Fintype.piFinset S : Finset (∀ i, G i)) : Set (∀ i, G i)) := by
    intro x hx y hy hxy hcomm
    simp only [Finset.mem_coe, Fintype.mem_piFinset] at hx hy
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    refine hS i (hx i) (hy i) hi ?_
    have hc : x * y = y * x := hcomm
    have h1 := congrFun hc i
    simp only [Pi.mul_apply] at h1
    exact h1
  have h2 := card_le_omegaG _ hnc
  refine le_trans ?_ h2
  have h3 : (∏ i, m i) ≤ (Fintype.piFinset S).card := by
    rw [Fintype.card_piFinset]
    exact Finset.prod_le_prod' (fun i _ => hcard i)
  exact_mod_cast h3

/-- Products of abelian covers are abelian covers of the product. -/
theorem aG_pi_le {ι : Type} [Fintype ι] (G : ι → Type) [∀ i, Group (G i)] (k : ι → ℕ)
    (hk : ∀ i, aG (G i) ≤ (k i : ℕ∞)) :
    aG (∀ i, G i) ≤ ((∏ i, k i : ℕ) : ℕ∞) := by
  classical
  choose C hC1 hC2 hC3 using fun i => exists_cover_of_aG_le (k i) (hk i)
  have hcov : IsAbelianCover
      ((Fintype.piFinset C).image (fun A => Subgroup.pi Set.univ A)) := by
    constructor
    · intro B hB
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
      rw [Fintype.mem_piFinset] at hA
      intro u hu v hv
      have hcomm : ∀ i, u i * v i = v i * u i := by
        intro i
        have hui : u i ∈ A i := (Subgroup.mem_pi _).mp hu i (Set.mem_univ i)
        have hvi : v i ∈ A i := (Subgroup.mem_pi _).mp hv i (Set.mem_univ i)
        exact hC1 i (A i) (hA i) _ hui _ hvi
      show u * v = v * u
      funext i
      exact hcomm i
    · intro g
      choose A hA hgA using fun i => hC2 i (g i)
      refine ⟨Subgroup.pi Set.univ A, Finset.mem_image_of_mem _
        (Fintype.mem_piFinset.mpr hA), ?_⟩
      exact (Subgroup.mem_pi _).mpr (fun i _ => hgA i)
  refine le_trans (aG_le_of_cover _ hcov) ?_
  have hcard : ((Fintype.piFinset C).image
      (fun A => Subgroup.pi Set.univ A)).card ≤ ∏ i, k i := by
    refine le_trans Finset.card_image_le ?_
    rw [Fintype.card_piFinset]
    exact Finset.prod_le_prod' (fun i _ => hC3 i)
  exact_mod_cast hcard

/-- The covering cost of a direct product is at most the sum of the costs of the factors. -/
theorem log2a_pi_le_sum {ι : Type} [Fintype ι] (G : ι → Type) [∀ i, Group (G i)]
    [∀ i, Finite (G i)] : log2a (∀ i, G i) ≤ ∑ i, log2a (G i) := by
  classical
  have hk : ∀ i, aG (G i) ≤ (((aG (G i)).toNat : ℕ) : ℕ∞) :=
    fun i => le_of_eq (ENat.natCast_toNat aG_ne_top).symm
  have hle := aG_pi_le G (fun i => (aG (G i)).toNat) hk
  have htoNat : (aG (∀ i, G i)).toNat ≤ ∏ i, (aG (G i)).toNat := by
    have h1 := ENat.toNat_le_toNat hle (ENat.natCast_ne_top _)
    rwa [ENat.toNat_natCast] at h1
  have hpos : (0 : ℝ) < ((aG (∀ i, G i)).toNat : ℝ) := by
    exact_mod_cast one_le_aG_toNat
  have hne : ∀ i ∈ (Finset.univ : Finset ι), (((aG (G i)).toNat : ℕ) : ℝ) ≠ 0 := by
    intro i _
    have h1 : 1 ≤ (aG (G i)).toNat := one_le_aG_toNat
    exact Nat.cast_ne_zero.mpr (by omega)
  have hlog : log2a (∀ i, G i) ≤ Real.logb 2 ((∏ i, (aG (G i)).toNat : ℕ) : ℝ) := by
    unfold log2a
    refine Real.logb_le_logb_of_le (by norm_num) hpos ?_
    exact_mod_cast htoNat
  refine le_trans hlog (le_of_eq ?_)
  calc Real.logb 2 ((∏ i, (aG (G i)).toNat : ℕ) : ℝ)
      = Real.logb 2 (∏ i, (((aG (G i)).toNat : ℕ) : ℝ)) := by rw [Nat.cast_prod]
    _ = ∑ i, Real.logb 2 (((aG (G i)).toNat : ℕ) : ℝ) := by
        simp only [Real.logb]
        rw [Real.log_prod hne, Finset.sum_div]
    _ = ∑ i, log2a (G i) := rfl

/-- A finite product of `p`-groups is a `p`-group. -/
theorem pi_isPGroup {ι : Type} [Fintype ι] {p : ℕ} [Fact p.Prime] (G : ι → Type)
    [∀ i, Group (G i)] [∀ i, Finite (G i)] (h : ∀ i, IsPGroup p (G i)) :
    IsPGroup p (∀ i, G i) := by
  classical
  choose ee he using fun i => (h i).exists_card_eq
  refine IsPGroup.of_card (n := ∑ i, ee i) ?_
  rw [Nat.card_pi, Finset.prod_congr rfl (fun i _ => he i)]
  exact Finset.prod_pow_eq_pow_sum _ _ _

/-! ### Arithmetic of the factor parameters -/

/-- `a + b ≤ ab` for naturals `a, b ≥ 3`. -/
theorem nat_add_le_mul {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) : a + b ≤ a * b := by
  nlinarith [ha, hb]

/-- A product of factors `≥ 3` over a nonempty index set is `≥ 3`. -/
theorem three_le_prod {ι : Type} {T : Finset ι} {m : ι → ℕ} (h : ∀ i ∈ T, 3 ≤ m i)
    (hne : T.Nonempty) : 3 ≤ ∏ i ∈ T, m i := by
  obtain ⟨j, hj⟩ := hne
  exact le_trans (h j hj) (Finset.single_le_prod' (fun i hi => le_trans (by norm_num) (h i hi)) hj)

/-- For factors `≥ 3` the sum is at most the product. -/
theorem sum_le_prod_of_three_le {ι : Type} (T : Finset ι) (m : ι → ℕ) :
    (∀ i ∈ T, 3 ≤ m i) → ∑ i ∈ T, m i ≤ ∏ i ∈ T, m i := by
  classical
  induction T using Finset.induction_on with
  | empty => intro _; simp
  | insert j T' hj ih =>
      intro h
      rw [Finset.sum_insert hj, Finset.prod_insert hj]
      have hmj : 3 ≤ m j := h j (Finset.mem_insert_self j T')
      have h' : ∀ i ∈ T', 3 ≤ m i := fun i hi => h i (Finset.mem_insert_of_mem hi)
      rcases T'.eq_empty_or_nonempty with rfl | hTne
      · simp
      · have hP := three_le_prod h' hTne
        have hSP := ih h'
        have hkey := nat_add_le_mul hmj hP
        exact le_trans (Nat.add_le_add_left hSP _) hkey


/-- `√3 ≤ √m` for `m ≥ 3`, in the convenient form `1.7 ≤ √m`. -/
theorem sqrt_ge_of_three_le {m : ℕ} (h : 3 ≤ m) : (1.7 : ℝ) ≤ Real.sqrt m := by
  have h1 : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
  have h2 : (1.7 : ℝ) = Real.sqrt (1.7 ^ 2) := by
    rw [Real.sqrt_sq (by norm_num)]
  rw [h2]
  apply Real.sqrt_le_sqrt
  norm_num
  linarith

/-- For factors `≥ 3` the sum of square roots is at most `1.5` times the square root of the
product. -/
theorem sum_sqrt_le_of_three_le {ι : Type} (T : Finset ι) (m : ι → ℕ) :
    (∀ i ∈ T, 3 ≤ m i) →
      ∑ i ∈ T, Real.sqrt (m i) ≤ 1.5 * Real.sqrt ((∏ i ∈ T, m i : ℕ)) := by
  classical
  induction T using Finset.induction_on with
  | empty => intro _; simp; norm_num
  | insert j T' hj ih =>
      intro h
      rw [Finset.sum_insert hj, Finset.prod_insert hj]
      have hmj : 3 ≤ m j := h j (Finset.mem_insert_self j T')
      have h' : ∀ i ∈ T', 3 ≤ m i := fun i hi => h i (Finset.mem_insert_of_mem hi)
      have hcast : (((m j * ∏ i ∈ T', m i : ℕ)) : ℝ) = (m j : ℝ) * ((∏ i ∈ T', m i : ℕ) : ℝ) := by
        push_cast; ring
      rw [hcast, Real.sqrt_mul (Nat.cast_nonneg _)]
      set q : ℝ := Real.sqrt (m j) with hq
      set P : ℝ := Real.sqrt ((∏ i ∈ T', m i : ℕ)) with hP
      have hq0 : 0 ≤ q := Real.sqrt_nonneg _
      have hP0 : 0 ≤ P := Real.sqrt_nonneg _
      have hq17 : (1.7 : ℝ) ≤ q := sqrt_ge_of_three_le hmj
      rcases T'.eq_empty_or_nonempty with rfl | hTne
      · simp only [Finset.sum_empty, Finset.prod_empty, Nat.cast_one, Real.sqrt_one] at *
        rw [hP]
        norm_num
        linarith
      · have hSP := ih h'
        have hP17 : (1.7 : ℝ) ≤ P := by
          rw [hP]
          have h3 : 3 ≤ ∏ i ∈ T', m i := three_le_prod h' hTne
          exact sqrt_ge_of_three_le h3
        nlinarith [hSP, hq17, hP17, mul_nonneg hq0 hP0]

/-- With at least two factors, the sum of factors `≥ 3` is at most two thirds of the product. -/
theorem sum_le_two_thirds_prod {ι : Type} (T : Finset ι) (m : ι → ℕ)
    (h : ∀ i ∈ T, 3 ≤ m i) {i₀ i₁ : ι} (h0 : i₀ ∈ T) (h1 : i₁ ∈ T) (hne : i₀ ≠ i₁) :
    3 * ∑ i ∈ T, m i ≤ 2 * ∏ i ∈ T, m i := by
  classical
  have hins : insert i₀ (T.erase i₀) = T := Finset.insert_erase h0
  have hi1 : i₁ ∈ T.erase i₀ := Finset.mem_erase.mpr ⟨(Ne.symm hne), h1⟩
  have hTne : (T.erase i₀).Nonempty := ⟨i₁, hi1⟩
  have h' : ∀ i ∈ T.erase i₀, 3 ≤ m i := fun i hi => h i (Finset.mem_of_mem_erase hi)
  have hsum : ∑ i ∈ T, m i = m i₀ + ∑ i ∈ T.erase i₀, m i := by
    conv_lhs => rw [← hins]
    exact Finset.sum_insert (Finset.notMem_erase _ _)
  have hprod : ∏ i ∈ T, m i = m i₀ * ∏ i ∈ T.erase i₀, m i := by
    conv_lhs => rw [← hins]
    exact Finset.prod_insert (Finset.notMem_erase _ _)
  have hS := sum_le_prod_of_three_le (T.erase i₀) m h'
  have hP3 := three_le_prod h' hTne
  have hm0 := h i₀ h0
  rw [hsum, hprod]
  nlinarith [hS, hP3, hm0]

/-- `n³ < 2ⁿ` for `n ≥ 10`. -/
theorem cube_lt_two_pow_of_ten_le : ∀ n : ℕ, 10 ≤ n → n ^ 3 < 2 ^ n := by
  intro n hn
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 10 with hk | hk
    · interval_cases k <;> omega
    · have h1 := ih hk
      have hk2 : 10 * k ^ 2 ≤ k ^ 3 := by
        calc 10 * k ^ 2 ≤ k * k ^ 2 := Nat.mul_le_mul_right _ hk
          _ = k ^ 3 := by ring
      have hk3 : 3 * k + 1 ≤ 7 * k ^ 2 := by nlinarith
      have h2 : (k + 1) ^ 3 ≤ 2 * k ^ 3 := by nlinarith [hk2, hk3]
      calc (k + 1) ^ 3 ≤ 2 * k ^ 3 := h2
        _ < 2 * 2 ^ k := Nat.mul_lt_mul_of_pos_left h1 (by norm_num)
        _ = 2 ^ (k + 1) := by ring

/-- **Remark 4.5**, uniform form: for every odd prime `q` one has `α_q ≤ 0.47`, so the odd
primes are uniformly cheaper than `p = 2`. -/
theorem alphaP_le_of_odd {q : ℕ} (hq : q.Prime) (h2 : q ≠ 2) : alphaP q ≤ 0.47 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rcases eq_or_ne q 3 with rfl | h3
  · linarith [alphaP_three_lt]
  have h4 : q ≠ 4 := by
    rintro rfl
    norm_num at hq
  have h5 : 5 ≤ q := by
    have := hq.two_le
    omega
  have hk : kappa q = (q : ℝ) / 2 := by simp [kappa, h2, h3]
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    have : (0 : ℕ) < q := by omega
    exact_mod_cast this
  have halpha : alphaP q = Real.log q / ((q : ℝ) * Real.log 2) := by
    rw [alphaP, hk, show (2 : ℝ) * ((q : ℝ) / 2) = (q : ℝ) by ring, Real.logb, div_div,
      mul_comm (Real.log 2) ((q : ℝ))]
  rw [halpha, div_le_iff₀ (by positivity)]
  rcases eq_or_ne q 5 with rfl | h5'
  · have hp : ((5 : ℝ)) ^ (3 : ℕ) ≤ (2 : ℝ) ^ (7 : ℕ) := by norm_num
    have h := Real.log_le_log (by positivity) hp
    rw [Real.log_pow, Real.log_pow] at h
    push_cast
    push_cast at h
    linarith
  rcases eq_or_ne q 7 with rfl | h7'
  · have hp : ((7 : ℝ)) ^ (2 : ℕ) ≤ (2 : ℝ) ^ (6 : ℕ) := by norm_num
    have h := Real.log_le_log (by positivity) hp
    rw [Real.log_pow, Real.log_pow] at h
    push_cast
    push_cast at h
    linarith
  · have h10 : 10 ≤ q := by
      by_contra hc
      push Not at hc
      interval_cases q <;> simp_all <;> norm_num at hq
    have hpow : ((q : ℝ)) ^ (3 : ℕ) < (2 : ℝ) ^ (q : ℕ) := by
      exact_mod_cast cube_lt_two_pow_of_ten_le q h10
    have h := Real.log_lt_log (by positivity) hpow
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    nlinarith [mul_nonneg hqpos.le hlog2.le]

/-! ### The nilpotent bound -/

/-- A product of abelian groups is abelian. -/
theorem pi_commute_of_forall {ι : Type} (G : ι → Type) [∀ i, Group (G i)]
    (h : ∀ i, ∀ x y : G i, Commute x y) : ∀ x y : (∀ i, G i), Commute x y := by
  intro x y
  funext i
  exact h i (x i) (y i)

/-- The core estimate: a finite direct product of `p`-groups (with varying primes) satisfies the
same bounds as a single `p`-group, with an improvement when at least two factors are nonabelian
and a further improvement when all nonabelian factors sit at odd primes. -/
theorem pi_pgroup_bound (hNVL : NeumannVaughanLeeBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type) [Fintype ι] (pr : ι → ℕ) (G : ι → Type)
      [∀ i, Group (G i)] [∀ i, Finite (G i)],
      (∀ i, Fact (pr i).Prime) → (∀ i, IsPGroup (pr i) (G i)) →
      ∀ n : ℕ, omegaG (∀ i, G i) = (n : ℕ∞) →
      log2a (∀ i, G i) ≤ (n : ℝ) / 2 + C * Real.sqrt n * (Real.log (n + 2)) ^ 3 ∧
      ((∃ i₀ i₁ : ι, i₀ ≠ i₁ ∧ (¬ ∀ x y : G i₀, Commute x y) ∧
          (¬ ∀ x y : G i₁, Commute x y)) →
        log2a (∀ i, G i) ≤ (n : ℝ) / 3 + C * Real.sqrt n * (Real.log (n + 2)) ^ 3) ∧
      ((∀ i : ι, (¬ ∀ x y : G i, Commute x y) → pr i ≠ 2) →
        log2a (∀ i, G i) ≤ 0.47 * (n : ℝ) + C * Real.sqrt n * (Real.log (n + 2)) ^ 3) := by
  classical
  obtain ⟨C, hC, hp⟩ := pgroup_sqrt_bound hNVL
  refine ⟨1.5 * C, by linarith, ?_⟩
  intro ι _ pr G _ _ hpr hpg n hn
  have : ∀ i, Fact (pr i).Prime := hpr
  have hom : ∀ i, omegaG (G i) = (((omegaG (G i)).toNat : ℕ) : ℕ∞) :=
    fun i => (ENat.natCast_toNat omegaG_ne_top).symm
  have hnn1 : ∀ i, 1 ≤ (omegaG (G i)).toNat := by
    intro i
    have h1 := one_le_omegaG (G := G i)
    rw [hom i] at h1
    exact_mod_cast h1
  have hprodle : (∏ i, (omegaG (G i)).toNat) ≤ n := by
    have h1 : ((∏ i, (omegaG (G i)).toNat : ℕ) : ℕ∞) ≤ omegaG (∀ i, G i) :=
      omegaG_pi_ge G (fun i => (omegaG (G i)).toNat) (fun i => le_of_eq (hom i).symm)
    rw [hn] at h1
    exact_mod_cast h1
  have hnnle : ∀ i, (omegaG (G i)).toNat ≤ n := fun i =>
    le_trans (Finset.single_le_prod' (fun j _ => hnn1 j) (Finset.mem_univ i)) hprodle
  have hn1 : 1 ≤ n := by
    have h1 : (1 : ℕ∞) ≤ omegaG (∀ i, G i) := one_le_omegaG
    rw [hn] at h1
    exact_mod_cast h1
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  set lam : ℝ := Real.log ((n : ℝ) + 2) with hlam
  have hlam0 : 0 ≤ lam := Real.log_nonneg (by linarith)
  set T : Finset ι := Finset.univ.filter (fun i => ¬ ∀ x y : G i, Commute x y) with hT
  have hTsum : ∑ i ∈ T, log2a (G i) = ∑ i, log2a (G i) := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro i _ hi
    rw [hT, Finset.mem_filter] at hi
    simp only [Finset.mem_univ, true_and, not_not] at hi
    exact log2a_eq_zero_of_abelian hi
  have hT3 : ∀ i ∈ T, 3 ≤ (omegaG (G i)).toNat := by
    intro i hi
    rw [hT, Finset.mem_filter] at hi
    have h1 := three_le_omegaG_of_nonabelian hi.2
    rw [hom i] at h1
    exact_mod_cast h1
  have hbound0 : ∀ beta : ℝ, (∀ i ∈ T, alphaP (pr i) ≤ beta) → ∀ i ∈ T, log2a (G i)
      ≤ beta * ((omegaG (G i)).toNat : ℝ)
        + C * Real.sqrt ((omegaG (G i)).toNat) * lam ^ 3 := by
    intro beta hbeta i hi
    have h1 := hp (pr i) (G i) ((omegaG (G i)).toNat) (hpg i) (hom i)
    have h2 : alphaP (pr i) * ((omegaG (G i)).toNat : ℝ) ≤ beta * ((omegaG (G i)).toNat : ℝ) :=
      mul_le_mul_of_nonneg_right (hbeta i hi) (Nat.cast_nonneg _)
    have h5 : Real.log (((omegaG (G i)).toNat : ℝ) + 2) ≤ lam := by
      rw [hlam]
      refine Real.log_le_log (by positivity) ?_
      have h6 : ((omegaG (G i)).toNat : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnnle i
      linarith
    have h7 : Real.log (((omegaG (G i)).toNat : ℝ) + 2) ^ 3 ≤ lam ^ 3 := by
      have h8 : 0 ≤ Real.log (((omegaG (G i)).toNat : ℝ) + 2) := by
        refine Real.log_nonneg ?_
        have h0 : (0 : ℝ) ≤ ((omegaG (G i)).toNat : ℝ) := Nat.cast_nonneg _
        linarith
      exact pow_le_pow_left₀ h8 h5 3
    have h9 : C * Real.sqrt ((omegaG (G i)).toNat)
        * Real.log (((omegaG (G i)).toNat : ℝ) + 2) ^ 3
        ≤ C * Real.sqrt ((omegaG (G i)).toNat) * lam ^ 3 :=
      mul_le_mul_of_nonneg_left h7 (by positivity)
    linarith
  have hsum1 : ∀ beta : ℝ, (∀ i ∈ T, alphaP (pr i) ≤ beta) →
      log2a (∀ i, G i) ≤ beta * (∑ i ∈ T, ((omegaG (G i)).toNat : ℝ))
        + C * lam ^ 3 * ∑ i ∈ T, Real.sqrt ((omegaG (G i)).toNat) := by
    intro beta hbeta
    have h1 : log2a (∀ i, G i) ≤ ∑ i ∈ T, log2a (G i) := by
      rw [hTsum]; exact log2a_pi_le_sum G
    refine le_trans h1 ?_
    refine le_trans (Finset.sum_le_sum (hbound0 beta hbeta)) ?_
    have heq2 : ∑ i ∈ T, (C * Real.sqrt ((omegaG (G i)).toNat) * lam ^ 3)
        = C * lam ^ 3 * ∑ i ∈ T, Real.sqrt ((omegaG (G i)).toNat) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, heq2]
  -- the product of the selected parameters is at most `n`
  have hTprod : (∏ i ∈ T, (omegaG (G i)).toNat) ≤ n := by
    refine le_trans ?_ hprodle
    refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
    intro i _ _
    exact hnn1 i
  have hsqrt : ∑ i ∈ T, Real.sqrt ((omegaG (G i)).toNat) ≤ 1.5 * Real.sqrt n := by
    refine le_trans (sum_sqrt_le_of_three_le T _ hT3) ?_
    have h1 : ((∏ i ∈ T, (omegaG (G i)).toNat : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hTprod
    have h2 : Real.sqrt ((∏ i ∈ T, (omegaG (G i)).toNat : ℕ)) ≤ Real.sqrt n :=
      Real.sqrt_le_sqrt h1
    linarith
  have hCl : 0 ≤ C * lam ^ 3 := by positivity
  have h3 : C * lam ^ 3 * ∑ i ∈ T, Real.sqrt ((omegaG (G i)).toNat)
      ≤ C * lam ^ 3 * (1.5 * Real.sqrt n) := mul_le_mul_of_nonneg_left hsqrt hCl
  have h4 : C * lam ^ 3 * (1.5 * Real.sqrt n) = 1.5 * C * Real.sqrt n * lam ^ 3 := by ring
  have hsumn0 : (∑ i ∈ T, ((omegaG (G i)).toNat : ℝ)) ≤ (n : ℝ) := by
    have h1 := sum_le_prod_of_three_le T _ hT3
    have h2 : (∑ i ∈ T, (omegaG (G i)).toNat) ≤ n := le_trans h1 hTprod
    exact_mod_cast h2
  have hsumnn : (0 : ℝ) ≤ ∑ i ∈ T, ((omegaG (G i)).toNat : ℝ) :=
    Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
  refine ⟨?_, ?_, ?_⟩
  · have hs := hsum1 (1 / 2) (fun i _ => alphaP_le_half (hpr i).out)
    linarith [hs, hsumn0, h3]
  · rintro ⟨i₀, i₁, hne, ha0, ha1⟩
    have hi0 : i₀ ∈ T := by
      rw [hT, Finset.mem_filter]; exact ⟨Finset.mem_univ _, ha0⟩
    have hi1 : i₁ ∈ T := by
      rw [hT, Finset.mem_filter]; exact ⟨Finset.mem_univ _, ha1⟩
    have hsumn : 3 * (∑ i ∈ T, ((omegaG (G i)).toNat : ℝ)) ≤ 2 * (n : ℝ) := by
      have h1 : 3 * (∑ i ∈ T, (omegaG (G i)).toNat)
          ≤ 2 * ∏ i ∈ T, (omegaG (G i)).toNat :=
        sum_le_two_thirds_prod T (fun i => (omegaG (G i)).toNat) hT3 hi0 hi1 hne
      have h2 : 3 * (∑ i ∈ T, (omegaG (G i)).toNat) ≤ 2 * n :=
        le_trans h1 (Nat.mul_le_mul_left 2 hTprod)
      exact_mod_cast h2
    have hs := hsum1 (1 / 2) (fun i _ => alphaP_le_half (hpr i).out)
    linarith [hs, hsumn, h3]
  · intro hodd
    have hbeta : ∀ i ∈ T, alphaP (pr i) ≤ 0.47 := by
      intro i hi
      rw [hT, Finset.mem_filter] at hi
      exact alphaP_le_of_odd (hpr i).out (hodd i hi.2)
    have hs := hsum1 0.47 hbeta
    have h5 : (0.47 : ℝ) * (∑ i ∈ T, ((omegaG (G i)).toNat : ℝ)) ≤ 0.47 * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hsumn0 (by norm_num)
    linarith [hs, h5, h3]

/-- The Sylow decomposition of a finite nilpotent group. -/
theorem nilpotent_sylow_decomposition (F : Type) [Group F] [Finite F]
    (h : Group.IsNilpotent F) :
    Nonempty ((∀ p : (Nat.card F).primeFactors, ∀ P : Sylow (p : ℕ) F,
      (P : Subgroup F)) ≃* F) :=
  letI : Group.IsNilpotent F := h
  ⟨Sylow.directProductOfNormal (fun {_p _hp _P} => inferInstance)⟩

/-- A nonabelian Sylow `q`-subgroup forces `q` to divide the order of the group. -/
theorem mem_primeFactors_of_nonabelian_sylow {F : Type} [Group F] [Finite F] {q : ℕ}
    (hq : q.Prime) (Q : Sylow q F) (hQ : ¬ ∀ x y : Q, Commute x y) :
    q ∈ (Nat.card F).primeFactors := by
  have : Fact q.Prime := ⟨hq⟩
  have hnt : Nontrivial (Q : Subgroup F) := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    exact hQ (fun x y => by
      have : x = y := Subsingleton.elim x y
      rw [this])
  obtain ⟨k, hk⟩ := (Q.isPGroup').exists_card_eq
  have hcard1 : 1 < Nat.card (Q : Subgroup F) := Finite.one_lt_card_iff_nontrivial.mpr hnt
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · rw [hk] at hcard1; simp at hcard1
    · exact h
  have hdvd1 : q ∣ Nat.card (Q : Subgroup F) := by
    rw [hk]
    exact dvd_pow_self q (by omega)
  have hdvd2 : Nat.card (Q : Subgroup F) ∣ Nat.card F := Subgroup.card_subgroup_dvd_card _
  have hne : Nat.card F ≠ 0 := Nat.card_pos.ne'
  exact Nat.mem_primeFactors.mpr ⟨hq, dvd_trans hdvd1 hdvd2, hne⟩

/-- If a single factor of a direct product is nonabelian, so is the product. -/
theorem nonabelian_pi_of_factor {ι : Type} (G : ι → Type) [∀ i, Group (G i)]
    (i : ι) (h : ¬ ∀ x y : G i, Commute x y) : ¬ ∀ x y : (∀ j, G j), Commute x y := by
  classical
  intro hcomm
  refine h (fun x y => ?_)
  have h1 : (Pi.mulSingle (M := G) i x) * (Pi.mulSingle (M := G) i y)
      = (Pi.mulSingle (M := G) i y) * (Pi.mulSingle (M := G) i x) := hcomm _ _
  have h2 := congrFun h1 i
  change x * y = y * x
  simpa [Pi.mulSingle_eq_same] using h2

/-- If some Sylow `q`-subgroup is nonabelian then the `q`-component of the Sylow decomposition is
nonabelian. -/
theorem nonabelian_pi_sylow {F : Type} [Group F] [Finite F] {q : ℕ} (Q : Sylow q F)
    (hQ : ¬ ∀ x y : Q, Commute x y) :
    ¬ ∀ x y : (∀ P : Sylow q F, (P : Subgroup F)), Commute x y :=
  nonabelian_pi_of_factor (fun P : Sylow q F => ((P : Subgroup F) : Type)) Q hQ

/-- **Theorem 7.1** (Nilpotent upper bound), quantitative form. -/
theorem nilpotent_sqrt_bound (hNVL : NeumannVaughanLeeBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Type) [Group F] [Finite F] (n : ℕ),
      Group.IsNilpotent F → omegaG F = (n : ℕ∞) →
      log2a F ≤ (n : ℝ) / 2 + C * Real.sqrt n * (Real.log (n + 2)) ^ 3 ∧
      ((∃ (q₁ q₂ : ℕ) (_ : q₁.Prime) (_ : q₂.Prime) (Q₁ : Sylow q₁ F) (Q₂ : Sylow q₂ F),
          q₁ ≠ q₂ ∧ (¬ ∀ x y : Q₁, Commute x y) ∧ (¬ ∀ x y : Q₂, Commute x y)) →
        log2a F ≤ (n : ℝ) / 3 + C * Real.sqrt n * (Real.log (n + 2)) ^ 3) ∧
      ((∀ (s : ℕ) (Q : Sylow s F), s = 2 → ∀ x y : Q, Commute x y) →
        log2a F ≤ 0.47 * (n : ℝ) + C * Real.sqrt n * (Real.log (n + 2)) ^ 3) := by
  classical
  obtain ⟨C, hC, hcore⟩ := pi_pgroup_bound hNVL
  refine ⟨C, hC, ?_⟩
  intro F _ _ n hnil hn
  let := Fintype.ofFinite F
  obtain ⟨e⟩ := nilpotent_sylow_decomposition F hnil
  have hom : omegaG (∀ p : (Nat.card F).primeFactors, ∀ P : Sylow (p : ℕ) F,
      (P : Subgroup F)) = (n : ℕ∞) := by
    rw [omegaG_eq_of_mulEquiv e]; exact hn
  have hlog : log2a (∀ p : (Nat.card F).primeFactors, ∀ P : Sylow (p : ℕ) F,
      (P : Subgroup F)) = log2a F := log2a_eq_of_mulEquiv e
  have hpr : ∀ p : (Nat.card F).primeFactors, Fact ((p : ℕ)).Prime :=
    fun p => ⟨Nat.prime_of_mem_primeFactors p.2⟩
  have hpg : ∀ p : (Nat.card F).primeFactors,
      IsPGroup (p : ℕ) (∀ P : Sylow (p : ℕ) F, (P : Subgroup F)) := by
    intro p
    have := hpr p
    exact pi_isPGroup _ (fun P => P.isPGroup')
  obtain ⟨hA, hB, hD⟩ := hcore ((Nat.card F).primeFactors) (fun p => (p : ℕ))
    (fun p => ∀ P : Sylow (p : ℕ) F, (P : Subgroup F)) hpr hpg n hom
  rw [hlog] at hA hB hD
  refine ⟨hA, ?_, ?_⟩
  · rintro ⟨q₁, q₂, hq₁, hq₂, Q₁, Q₂, hne, hQ₁, hQ₂⟩
    refine hB ⟨⟨q₁, mem_primeFactors_of_nonabelian_sylow hq₁ Q₁ hQ₁⟩,
      ⟨q₂, mem_primeFactors_of_nonabelian_sylow hq₂ Q₂ hQ₂⟩, ?_, ?_, ?_⟩
    · simp only [ne_eq, Subtype.mk.injEq]
      exact hne
    · exact nonabelian_pi_sylow Q₁ hQ₁
    · exact nonabelian_pi_sylow Q₂ hQ₂
  · intro h2ab
    refine hD ?_
    intro p hnonab hp2
    exact hnonab (pi_commute_of_forall _ (fun P => h2ab (p : ℕ) P hp2))

/-- **Theorem 7.1** (Nilpotent upper bound), first part: `log₂ a(F) ≤ n/2 + o(n)` uniformly over
finite nilpotent groups. -/
theorem nilpotent_upper_bound (hNVL : NeumannVaughanLeeBound) :
    ∃ eps : ℕ → ℝ, Filter.Tendsto eps Filter.atTop (nhds 0) ∧
      ∀ (F : Type) [Group F] [Finite F] (n : ℕ), Group.IsNilpotent F → omegaG F = (n : ℕ∞) →
        log2a F ≤ (n : ℝ) / 2 + eps n * n := by
  obtain ⟨C, hC, h⟩ := nilpotent_sqrt_bound hNVL
  refine ⟨fun n => C * ((Real.log ((n : ℝ) + 2)) ^ 3 / Real.sqrt n), ?_, ?_⟩
  · simpa using log_cube_div_sqrt_tendsto.const_mul C
  · intro F _ _ n hnil hn
    have h1 := (h F n hnil hn).1
    have hn1 : 1 ≤ n := by
      have h2 : (1 : ℕ∞) ≤ omegaG F := one_le_omegaG
      rw [hn] at h2
      exact_mod_cast h2
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hs : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
    have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
      Real.mul_self_sqrt (by linarith)
    have heq : C * ((Real.log ((n : ℝ) + 2)) ^ 3 / Real.sqrt n) * (n : ℝ)
        = C * Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3 := by
      field_simp
      rw [Real.sq_sqrt (by linarith : (0:ℝ) ≤ (n:ℝ))]
      ring
    rw [heq]
    exact h1

/-- **Theorem 7.1**, second part: with at least two nonabelian Sylow subgroups the bound improves
to `n/3 + o(n)`. -/
theorem nilpotent_upper_bound_two_sylow (hNVL : NeumannVaughanLeeBound) :
    ∃ eps : ℕ → ℝ, Filter.Tendsto eps Filter.atTop (nhds 0) ∧
      ∀ (F : Type) [Group F] [Finite F] (n : ℕ), Group.IsNilpotent F → omegaG F = (n : ℕ∞) →
        (∃ (q₁ q₂ : ℕ) (_ : q₁.Prime) (_ : q₂.Prime) (Q₁ : Sylow q₁ F) (Q₂ : Sylow q₂ F),
          q₁ ≠ q₂ ∧ (¬ ∀ x y : Q₁, Commute x y) ∧ (¬ ∀ x y : Q₂, Commute x y)) →
        log2a F ≤ (n : ℝ) / 3 + eps n * n := by
  obtain ⟨C, hC, h⟩ := nilpotent_sqrt_bound hNVL
  refine ⟨fun n => C * ((Real.log ((n : ℝ) + 2)) ^ 3 / Real.sqrt n), ?_, ?_⟩
  · simpa using log_cube_div_sqrt_tendsto.const_mul C
  · intro F _ _ n hnil hn htwo
    have h1 := (h F n hnil hn).2.1 htwo
    have hn1 : 1 ≤ n := by
      have h2 : (1 : ℕ∞) ≤ omegaG F := one_le_omegaG
      rw [hn] at h2
      exact_mod_cast h2
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hs : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
    have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
      Real.mul_self_sqrt (by linarith)
    have heq : C * ((Real.log ((n : ℝ) + 2)) ^ 3 / Real.sqrt n) * (n : ℝ)
        = C * Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3 := by
      field_simp
      rw [Real.sq_sqrt (by linarith : (0:ℝ) ≤ (n:ℝ))]
      ring
    rw [heq]
    exact h1

/-! ## 8. Extension from a nilpotent normal subgroup -/

/-- The subgroup generated by a set of pairwise commuting elements is abelian. -/
theorem commute_of_mem_closure_commuting {G : Type} [Group G] (s : Set G)
    (h : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    ∀ x ∈ Subgroup.closure s, ∀ y ∈ Subgroup.closure s, Commute x y := by
  intro x hx y hy
  have h1 : Subgroup.closure s ≤ Subgroup.centralizer s := by
    rw [Subgroup.closure_le]
    intro a ha m hm
    exact (h a ha m hm).symm
  have h2 : Subgroup.closure s ≤ Subgroup.centralizer (Subgroup.centralizer s : Set G) :=
    Subgroup.closure_le_centralizer_centralizer s
  exact ((h2 hx) y (h1 hy)).symm

/-- A greedy covering estimate: in a finite "graph" in which every nonempty invariant set `R`
contains a vertex whose neighbourhood meets `R` in at least a `1/B` fraction, and in which every
nonempty invariant set has at least `Z0c` elements, one can dominate the whole vertex set by
`m` vertices as soon as `|Xf| (B-1)^m < Z0c B^m`. -/
theorem greedy_cover {α : Type*} [DecidableEq α] (Xf : Finset α) (rel : α → α → Prop)
    [DecidableRel rel] (B Z0c : ℕ) (hB : 2 ≤ B)
    (Inv : Finset α → Prop)
    (hIsub : ∀ (R : Finset α) (x : α), Inv R → Inv (R.filter (fun y => ¬ rel x y)))
    (hIcard : ∀ R : Finset α, Inv R → R.Nonempty → Z0c ≤ R.card)
    (hpick : ∀ R : Finset α, R ⊆ Xf → R.Nonempty →
      ∃ x ∈ Xf, R.card ≤ B * (R.filter (rel x)).card) :
    ∀ (m : ℕ) (R : Finset α), R ⊆ Xf → Inv R →
      (R.card : ℝ) * ((B:ℝ) - 1) ^ m < (Z0c : ℝ) * (B:ℝ) ^ m →
      ∃ D : Finset α, D ⊆ Xf ∧ D.card ≤ m ∧ ∀ y ∈ R, ∃ x ∈ D, rel x y := by
  have hB0 : (0:ℝ) < (B:ℝ) := by
    have : (2:ℝ) ≤ (B:ℝ) := by exact_mod_cast hB
    linarith
  have hB1 : (0:ℝ) < (B:ℝ) - 1 := by
    have : (2:ℝ) ≤ (B:ℝ) := by exact_mod_cast hB
    linarith
  intro m
  induction m with
  | zero =>
      intro R hRX hInv hcard
      simp only [pow_zero, mul_one] at hcard
      refine ⟨∅, Finset.empty_subset _, by simp, ?_⟩
      intro y hy
      exfalso
      have h1 := hIcard R hInv ⟨y, hy⟩
      have h2 : (Z0c : ℝ) ≤ (R.card : ℝ) := by exact_mod_cast h1
      linarith
  | succ m ih =>
      intro R hRX hInv hcard
      rcases Finset.eq_empty_or_nonempty R with rfl | hne
      · exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
      obtain ⟨x, hxX, hx⟩ := hpick R hRX hne
      set R' : Finset α := R.filter (fun y => ¬ rel x y) with hR'
      have hsplit : (R.filter (rel x)).card + R'.card = R.card :=
        Finset.card_filter_add_card_filter_not (rel x)
      have hstep : B * R'.card ≤ (B - 1) * R.card := by
        have h1 : B * R'.card + B * (R.filter (rel x)).card = B * R.card := by
          rw [← Nat.mul_add, Nat.add_comm R'.card, hsplit]
        have h2 : (B - 1) * R.card = B * R.card - R.card := by
          cases B with
          | zero => omega
          | succ b => simp [Nat.succ_mul]
        omega
      have hBsub : (((B - 1 : ℕ)) : ℝ) = (B:ℝ) - 1 := by
        have h1 : 1 ≤ B := by omega
        push_cast [Nat.cast_sub h1]
        ring
      have hstepR : (B:ℝ) * (R'.card : ℝ) ≤ ((B:ℝ) - 1) * (R.card : ℝ) := by
        calc (B:ℝ) * (R'.card : ℝ) ≤ (((B - 1 : ℕ)) : ℝ) * (R.card : ℝ) := by
              exact_mod_cast hstep
          _ = ((B:ℝ) - 1) * (R.card : ℝ) := by rw [hBsub]
      have hcard' : (R'.card : ℝ) * ((B:ℝ) - 1) ^ m < (Z0c : ℝ) * (B:ℝ) ^ m := by
        have h1 : (B:ℝ) * ((R'.card : ℝ) * ((B:ℝ) - 1) ^ m)
            ≤ (R.card : ℝ) * ((B:ℝ) - 1) ^ (m + 1) := by
          calc (B:ℝ) * ((R'.card : ℝ) * ((B:ℝ) - 1) ^ m)
              = ((B:ℝ) * (R'.card : ℝ)) * ((B:ℝ) - 1) ^ m := by ring
            _ ≤ (((B:ℝ) - 1) * (R.card : ℝ)) * ((B:ℝ) - 1) ^ m :=
                mul_le_mul_of_nonneg_right hstepR (pow_nonneg hB1.le m)
            _ = (R.card : ℝ) * ((B:ℝ) - 1) ^ (m + 1) := by ring
        have h3 : (R.card : ℝ) * ((B:ℝ) - 1) ^ (m + 1) < (B:ℝ) * ((Z0c : ℝ) * (B:ℝ) ^ m) := by
          have h4 : (Z0c : ℝ) * (B:ℝ) ^ (m + 1) = (B:ℝ) * ((Z0c : ℝ) * (B:ℝ) ^ m) := by ring
          linarith [hcard]
        exact lt_of_mul_lt_mul_left (lt_of_le_of_lt h1 h3) (le_of_lt hB0)
      have hR'X : R' ⊆ Xf := Finset.Subset.trans (Finset.filter_subset _ _) hRX
      obtain ⟨D, hDX, hDcard, hDdom⟩ := ih R' hR'X (hIsub R x hInv) hcard'
      refine ⟨insert x D, Finset.insert_subset hxX hDX, ?_, ?_⟩
      · exact le_trans (Finset.card_insert_le _ _) (by omega)
      · intro y hy
        by_cases hrel : rel x y
        · exact ⟨x, Finset.mem_insert_self _ _, hrel⟩
        · obtain ⟨z, hz, hzy⟩ := hDdom y (Finset.mem_filter.mpr ⟨hy, hrel⟩)
          exact ⟨z, Finset.mem_insert_of_mem hz, hzy⟩

/-- Inside a coset `gF`, the elements commuting with a fixed `y` of the coset are exactly the
translates by `y` of the elements of `F` commuting with `y`. -/
theorem coset_commuting_card {G : Type} [Group G] [Fintype G] (F : Subgroup G) (g y : G)
    (hy : g⁻¹ * y ∈ F) :
    ((Finset.univ.filter (fun x => g⁻¹ * x ∈ F)).filter (fun x => x * y = y * x)).card
      = (Finset.univ.filter (fun z => z ∈ F ∧ z * y = y * z)).card := by
  rw [Finset.filter_filter]
  refine Finset.card_nbij' (fun x => y⁻¹ * x) (fun z => y * z) ?_ ?_ ?_ ?_
  · intro b hb
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hb ⊢
    obtain ⟨hb1, hb2⟩ := hb
    have hmem : y⁻¹ * b ∈ F := by
      have h2 : (g⁻¹ * y)⁻¹ * (g⁻¹ * b) = y⁻¹ * b := by group
      rw [← h2]
      exact F.mul_mem (F.inv_mem hy) hb1
    refine ⟨hmem, ?_⟩
    have h3 : y * (y⁻¹ * b) = b := by group
    rw [h3]
    calc y⁻¹ * b * y = y⁻¹ * (b * y) := by group
      _ = y⁻¹ * (y * b) := by rw [hb2]
      _ = b := by group
  · intro z hz
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hz ⊢
    obtain ⟨hz1, hz2⟩ := hz
    refine ⟨?_, ?_⟩
    · have h4 : g⁻¹ * (y * z) = (g⁻¹ * y) * z := by group
      rw [h4]
      exact F.mul_mem hy hz1
    · calc y * z * y = y * (z * y) := by group
        _ = y * (y * z) := by rw [hz2]
  · intro b _; group
  · intro z _; group

/-- The greedy selection step for Lemma 8.1: in a coset of `F`, every nonempty subset `R` has an
element of the coset commuting with at least a `1/B` fraction of `R`. -/
theorem coset_pick {G : Type} [Group G] [Fintype G] (F : Subgroup G) (g : G) (B : ℕ)
    (hB : ∀ x : G, (Subgroup.centralizer ({x} : Set G)).index ≤ B)
    (R : Finset G) (hR : R ⊆ Finset.univ.filter (fun x => g⁻¹ * x ∈ F)) (hne : R.Nonempty) :
    ∃ x ∈ Finset.univ.filter (fun x => g⁻¹ * x ∈ F),
      R.card ≤ B * (R.filter (fun y => x * y = y * x)).card := by
  set Xf : Finset G := Finset.univ.filter (fun x => g⁻¹ * x ∈ F) with hXfdef
  have hXcard : Xf.card = Nat.card F := by
    have h1 : Xf.card = (Finset.univ.filter (fun z => z ∈ F)).card := by
      refine Finset.card_nbij' (fun x => g⁻¹ * x) (fun z => g * z) ?_ ?_ ?_ ?_ <;>
        intro b hb <;> simp_all
    rw [h1, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hdeg : ∀ y ∈ Xf, Xf.card ≤ B * (Xf.filter (fun x => x * y = y * x)).card := by
    intro y hy
    have hyF : g⁻¹ * y ∈ F := by simpa [hXfdef] using hy
    have h1 : (Xf.filter (fun x => x * y = y * x)).card
        = Nat.card (F ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) := by
      rw [hXfdef, coset_commuting_card F g y hyF, Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 1
      apply Finset.filter_congr
      intro z _
      simp [Subgroup.mem_centralizer_iff, eq_comm]
    rw [hXcard, h1]
    set C : Subgroup G := Subgroup.centralizer ({y} : Set G) with hC
    have hle : (F ⊓ C : Subgroup G) ≤ F := inf_le_left
    have h2 : Nat.card (((F ⊓ C : Subgroup G).subgroupOf F)) * ((F ⊓ C : Subgroup G).relIndex F)
        = Nat.card F := Subgroup.card_mul_index _
    have h3 : Nat.card (((F ⊓ C : Subgroup G).subgroupOf F)) = Nat.card (F ⊓ C : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    have h4 : (F ⊓ C : Subgroup G).relIndex F = C.relIndex F := by
      rw [inf_comm]; exact Subgroup.inf_relIndex_right C F
    have h5 : C.relIndex F ≤ C.index := by
      have h6 := Subgroup.relIndex_le_of_le_right (H := C) (K := F) (L := ⊤) le_top
        (by rw [Subgroup.relIndex_top_right]; exact Subgroup.index_ne_zero_of_finite)
      rwa [Subgroup.relIndex_top_right] at h6
    rw [h3, h4] at h2
    calc Nat.card F = Nat.card (F ⊓ C : Subgroup G) * C.relIndex F := h2.symm
      _ ≤ Nat.card (F ⊓ C : Subgroup G) * B := Nat.mul_le_mul_left _ (le_trans h5 (hB y))
      _ = B * Nat.card (F ⊓ C : Subgroup G) := Nat.mul_comm _ _
  have hXne : Xf.Nonempty := hne.mono hR
  have hswap : ∑ x ∈ Xf, (R.filter (fun y => x * y = y * x)).card
      = ∑ y ∈ R, (Xf.filter (fun x => x * y = y * x)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hsum : ∑ _x ∈ Xf, R.card ≤ ∑ x ∈ Xf, B * (R.filter (fun y => x * y = y * x)).card := by
    have h1 : ∑ _x ∈ Xf, R.card = ∑ _y ∈ R, Xf.card := by
      simp [Finset.sum_const, mul_comm]
    have h2 : ∑ _y ∈ R, Xf.card ≤ ∑ y ∈ R, B * (Xf.filter (fun x => x * y = y * x)).card :=
      Finset.sum_le_sum (fun y hy => hdeg y (hR hy))
    have h3 : ∑ y ∈ R, B * (Xf.filter (fun x => x * y = y * x)).card
        = B * ∑ y ∈ R, (Xf.filter (fun x => x * y = y * x)).card := by rw [Finset.mul_sum]
    have h4 : ∑ x ∈ Xf, B * (R.filter (fun y => x * y = y * x)).card
        = B * ∑ x ∈ Xf, (R.filter (fun y => x * y = y * x)).card := by rw [Finset.mul_sum]
    rw [h1, h4, hswap, ← h3]
    exact h2
  exact Finset.exists_le_of_sum_le hXne hsum

/-- The covering step of Lemma 8.1: a dominating set `D` of the coset `gF` together with an
abelian cover of `F` yields an abelian cover of the coset by `|D| a(F)` subgroups of `G`. -/
theorem coset_cover_step {G : Type} [Group G] [Fintype G] (F : Subgroup G) (g : G)
    (D : Finset G) (hD : ∀ x ∈ D, g⁻¹ * x ∈ F)
    (C : Finset (Subgroup (F : Type _))) (a : ℕ)
    (hCab : ∀ A ∈ C, ∀ x ∈ A, ∀ y ∈ A, Commute x y)
    (hCcov : ∀ z : (F : Type _), ∃ A ∈ C, z ∈ A) (hCcard : C.card ≤ a)
    (hdom : ∀ y : G, g⁻¹ * y ∈ F → ∃ x ∈ D, x * y = y * x) :
    aSet (g • (F : Set G)) ≤ ((D.card * a : ℕ) : ℕ∞) := by
  set W : G → Subgroup (F : Type _) → Subgroup G := fun x A =>
    Subgroup.closure (insert x
      ((A.map F.subtype ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G)) with hW
  have hWab : ∀ x : G, ∀ A ∈ C, ∀ u ∈ W x A, ∀ v ∈ W x A, Commute u v := by
    intro x A hA
    refine commute_of_mem_closure_commuting _ ?_
    intro u hu v hv
    have key : ∀ w ∈ (A.map F.subtype ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G),
        x * w = w * x := by
      intro w hw
      have h2 : w ∈ Subgroup.centralizer ({x} : Set G) := hw.2
      exact (Subgroup.mem_centralizer_iff.mp h2) x rfl
    rcases Set.mem_insert_iff.mp hu with rfl | hu'
    · rcases Set.mem_insert_iff.mp hv with rfl | hv'
      · rfl
      · exact key v hv'
    · rcases Set.mem_insert_iff.mp hv with rfl | hv'
      · exact (key u hu').symm
      · obtain ⟨u', hu'A, rfl⟩ := Subgroup.mem_map.mp hu'.1
        obtain ⟨v', hv'A, rfl⟩ := Subgroup.mem_map.mp hv'.1
        exact congrArg Subtype.val (hCab A hA u' hu'A v' hv'A)
  set cover : Finset (Subgroup G) := D.biUnion (fun x => C.image (fun A => W x A)) with hcover
  have hcard : cover.card ≤ D.card * a := by
    refine le_trans Finset.card_biUnion_le ?_
    calc ∑ x ∈ D, (C.image (fun A => W x A)).card ≤ ∑ _x ∈ D, a :=
          Finset.sum_le_sum (fun x _ => le_trans Finset.card_image_le hCcard)
      _ = D.card * a := by rw [Finset.sum_const, smul_eq_mul]
  have hcov : ∀ y ∈ g • (F : Set G), ∃ A ∈ cover, y ∈ A := by
    intro y hy
    have hyF : g⁻¹ * y ∈ F := by
      obtain ⟨f, hf, rfl⟩ := hy
      simpa using hf
    obtain ⟨x, hxD, hxy⟩ := hdom y hyF
    have hxF : g⁻¹ * x ∈ F := hD x hxD
    have hcF : x⁻¹ * y ∈ F := by
      have h2 : (g⁻¹ * x)⁻¹ * (g⁻¹ * y) = x⁻¹ * y := by group
      rw [← h2]
      exact F.mul_mem (F.inv_mem hxF) hyF
    obtain ⟨A, hA, hmem⟩ := hCcov ⟨x⁻¹ * y, hcF⟩
    refine ⟨W x A, Finset.mem_biUnion.mpr ⟨x, hxD, Finset.mem_image.mpr ⟨A, hA, rfl⟩⟩, ?_⟩
    have hc1 : x⁻¹ * y ∈ A.map F.subtype := ⟨⟨x⁻¹ * y, hcF⟩, hmem, rfl⟩
    have hc2 : x⁻¹ * y ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro m rfl
      calc m * (m⁻¹ * y) = y := by group
        _ = m⁻¹ * (m * y) := by group
        _ = m⁻¹ * (y * m) := by rw [hxy]
        _ = (m⁻¹ * y) * m := by group
    have hxW : x ∈ W x A := Subgroup.subset_closure (Set.mem_insert _ _)
    have hcW : x⁻¹ * y ∈ W x A :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨hc1, hc2⟩)
    have hyeq : y = x * (x⁻¹ * y) := by group
    rw [hyeq]
    exact (W x A).mul_mem hxW hcW
  have hk : ∀ A ∈ cover, aSet (A : Set G) ≤ ((1 : ℕ) : ℕ∞) := by
    intro A hA
    obtain ⟨x, hxD, hA'⟩ := Finset.mem_biUnion.mp hA
    obtain ⟨A', hA'C, rfl⟩ := Finset.mem_image.mp hA'
    simpa using aSet_le_one_of_abelian _ (hWab x A' hA'C)
  have hfin := aSet_le_of_subgroup_cover (g • (F : Set G)) cover 1 hcov hk
  simp only [mul_one] at hfin
  exact le_trans hfin (by exact_mod_cast hcard)

/-- The numerical estimate behind the choice of the size of the dominating set. -/
theorem coset_domination_numeric (B M m : ℕ) (hB : 2 ≤ B) (hM : 1 ≤ M)
    (hm : m = ⌈(B:ℝ) * Real.log M⌉₊ + 1) :
    (M:ℝ) * ((B:ℝ) - 1) ^ m < (B:ℝ) ^ m := by
  have hBR : (2:ℝ) ≤ (B:ℝ) := by exact_mod_cast hB
  have hB0 : (0:ℝ) < (B:ℝ) := by linarith
  have hMR : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hMR
  have h0 : (0:ℝ) ≤ 1 - 1/(B:ℝ) := by
    have h : 1/(B:ℝ) ≤ 1 := by rw [div_le_one hB0]; linarith
    linarith
  have h1 : 1 - 1/(B:ℝ) ≤ Real.exp (-(1/(B:ℝ))) := by
    have := Real.add_one_le_exp (-(1/(B:ℝ)))
    linarith
  have h2 : (1 - 1/(B:ℝ))^m ≤ (Real.exp (-(1/(B:ℝ))))^m := pow_le_pow_left₀ h0 h1 m
  have h3 : (Real.exp (-(1/(B:ℝ))))^m = Real.exp (-((m:ℝ)/(B:ℝ))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  have hmge : (B:ℝ) * Real.log M + 1 ≤ (m:ℝ) := by
    rw [hm]
    push_cast
    have := Nat.le_ceil ((B:ℝ) * Real.log M)
    linarith
  have h4 : Real.log M < (m:ℝ)/(B:ℝ) := by
    rw [lt_div_iff₀ hB0]
    nlinarith
  have h5 : Real.exp (-((m:ℝ)/(B:ℝ))) < 1/(M:ℝ) := by
    have h6 : Real.exp (-((m:ℝ)/(B:ℝ))) < Real.exp (-Real.log M) :=
      Real.exp_lt_exp.mpr (by linarith)
    have h7 : Real.exp (-Real.log M) = 1/(M:ℝ) := by
      rw [Real.exp_neg, Real.exp_log (by linarith)]
      simp
    linarith [h6, h7.le, h7.ge]
  have hkey : (1 - 1/(B:ℝ))^m < 1/(M:ℝ) := lt_of_le_of_lt (le_trans h2 (le_of_eq h3)) h5
  have hexp : (1 - 1/(B:ℝ))^m = ((B:ℝ) - 1)^m / (B:ℝ)^m := by
    rw [← div_pow]
    congr 1
    field_simp
  rw [hexp] at hkey
  have hBm : (0:ℝ) < (B:ℝ)^m := pow_pos hB0 m
  have hfin : (M:ℝ) * (((B:ℝ) - 1)^m / (B:ℝ)^m) < (M:ℝ) * (1/(M:ℝ)) :=
    mul_lt_mul_of_pos_left hkey (by linarith)
  rw [mul_one_div, div_self (by linarith : (M:ℝ) ≠ 0), mul_div_assoc', div_lt_one hBm] at hfin
  exact hfin


/-- **Lemma 8.1** (Coset domination): a coset of a subgroup `F` is covered by at most
`B (1 + log M) a(F)` abelian subgroups, where `M = [F : F ∩ Z(G)]`. -/
theorem coset_domination {G : Type} [Group G] [Finite G] (F : Subgroup G) (g : G) (B M : ℕ)
    (hB : ∀ x : G, (Subgroup.centralizer ({x} : Set G)).index ≤ B)
    (hM : M = ((F ⊓ Subgroup.center G).subgroupOf F).index) :
    ((aSet (g • (F : Set G))).toNat : ℝ) ≤
      (B : ℝ) * (1 + Real.log M) * ((aG (F : Type _)).toNat : ℝ) := by
  have := Fintype.ofFinite G
  set a : ℕ := (aG (F : Type _)).toNat with hadef
  obtain ⟨C, hCab, hCcov, hCcard⟩ := exists_cover_of_aG_le (G := (F : Type _)) a
    (by rw [hadef, ENat.natCast_toNat aG_ne_top])
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | h
    · exfalso
      rw [h0] at hCcard
      have hCe : C = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hCcard)
      obtain ⟨A, hA, -⟩ := hCcov 1
      rw [hCe] at hA
      exact absurd hA (Finset.notMem_empty _)
    · exact h
  have hB1 : 1 ≤ B := by
    have h1 := hB 1
    have h2 : (Subgroup.centralizer ({(1:G)} : Set G)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hM1 : 1 ≤ M := by
    rw [hM]
    have : ((F ⊓ Subgroup.center G).subgroupOf F).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM1)
  have haR : (1:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha1
  rcases eq_or_lt_of_le hB1 with hBeq | hB2
  · -- `B = 1`: every centraliser is the whole group, so `G` is abelian
    have habel : ∀ x y : G, x * y = y * x := by
      intro x y
      have h1 : (Subgroup.centralizer ({x} : Set G)).index = 1 := by
        have h0 := hB x
        have h2 : (Subgroup.centralizer ({x} : Set G)).index ≠ 0 :=
          Subgroup.index_ne_zero_of_finite
        omega
      have h3 : Subgroup.centralizer ({x} : Set G) = ⊤ := Subgroup.index_eq_one.mp h1
      have h4 : y ∈ Subgroup.centralizer ({x} : Set G) := by rw [h3]; trivial
      exact (Subgroup.mem_centralizer_iff.mp h4) x rfl
    have hone : aSet (g • (F : Set G)) ≤ ((1 * 1 : ℕ) : ℕ∞) := by
      refine aSet_le_of_subgroup_cover _ {(⊤ : Subgroup G)} 1 ?_ ?_
      · intro x _
        exact ⟨⊤, Finset.mem_singleton_self _, trivial⟩
      · intro A hA
        rw [Finset.mem_singleton] at hA
        subst hA
        simpa using aSet_le_one_of_abelian (⊤ : Subgroup G) (fun x _ y _ => habel x y)
    have htoNat : (aSet (g • (F : Set G))).toNat ≤ 1 := by
      have := ENat.toNat_le_toNat hone (by simp)
      simpa using this
    have h1R : ((aSet (g • (F : Set G))).toNat : ℝ) ≤ 1 := by exact_mod_cast htoNat
    have hBR : (B:ℝ) = 1 := by rw [← hBeq]; norm_num
    rw [hBR]
    nlinarith [hlogM, haR]
  · -- the main case `B ≥ 2`
    set Z0 : Subgroup G := F ⊓ Subgroup.center G with hZ0
    set Z0c : ℕ := Nat.card (Z0 : Type _) with hZ0c
    have hZ0pos : 0 < Z0c := Nat.card_pos
    have hFcard : Nat.card (F : Type _) = Z0c * M := by
      have h1 : Nat.card ((Z0.subgroupOf F)) * (Z0.subgroupOf F).index = Nat.card (F : Type _) :=
        Subgroup.card_mul_index _
      have h2 : Nat.card ((Z0.subgroupOf F)) = Z0c :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
      rw [h2, ← hM] at h1
      exact h1.symm
    set Xf : Finset G := Finset.univ.filter (fun x => g⁻¹ * x ∈ F) with hXf
    have hXcard : Xf.card = Nat.card (F : Type _) := by
      have h1 : Xf.card = (Finset.univ.filter (fun z => z ∈ F)).card := by
        refine Finset.card_nbij' (fun x => g⁻¹ * x) (fun z => g * z) ?_ ?_ ?_ ?_ <;>
          intro b hb <;> simp_all
      rw [h1, Nat.card_eq_fintype_card, Fintype.card_subtype]
    set Inv : Finset G → Prop := fun R => ∀ y ∈ R, ∀ z ∈ Z0, y * z ∈ R with hInvdef
    have hzc : ∀ z ∈ Z0, ∀ w : G, z * w = w * z := by
      intro z hz w
      have hzc' : z ∈ Subgroup.center G := hz.2
      exact (Subgroup.mem_center_iff.mp hzc' w).symm
    have hIsub : ∀ (R : Finset G) (x : G), Inv R →
        Inv (R.filter (fun y => ¬ (x * y = y * x))) := by
      intro R x hR y hy z hz
      rw [Finset.mem_filter] at hy ⊢
      refine ⟨hR y hy.1 z hz, ?_⟩
      intro hcon
      apply hy.2
      have e1 : x * (y * z) = (x * y) * z := by group
      have e2 : (y * z) * x = (y * x) * z := by
        calc (y * z) * x = y * (z * x) := by group
          _ = y * (x * z) := by rw [hzc z hz x]
          _ = (y * x) * z := by group
      rw [e1, e2] at hcon
      exact mul_right_cancel hcon
    have hIcard : ∀ R : Finset G, Inv R → R.Nonempty → Z0c ≤ R.card := by
      intro R hR hne
      obtain ⟨y, hy⟩ := hne
      have h1 : (Finset.univ.filter (fun z => z ∈ Z0)).card = Z0c := by
        rw [hZ0c, Nat.card_eq_fintype_card, Fintype.card_subtype]
      rw [← h1]
      refine Finset.card_le_card_of_injOn (fun z => y * z) ?_ ?_
      · intro z hz
        have hz' : z ∈ Z0 := by simpa using hz
        exact hR y hy z hz'
      · intro u _ v _ huv
        exact mul_left_cancel huv
    have hInvXf : Inv Xf := by
      intro y hy z hz
      rw [hXf, Finset.mem_filter] at hy ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      have e : g⁻¹ * (y * z) = (g⁻¹ * y) * z := by group
      rw [e]
      exact F.mul_mem hy.2 hz.1
    set m : ℕ := ⌈(B:ℝ) * Real.log M⌉₊ + 1 with hm
    have hlt : (Xf.card : ℝ) * ((B:ℝ) - 1) ^ m < (Z0c : ℝ) * (B:ℝ) ^ m := by
      rw [hXcard, hFcard]
      have h1 := coset_domination_numeric B M m hB2 hM1 hm
      have h2 : (0:ℝ) < (Z0c : ℝ) := by exact_mod_cast hZ0pos
      calc ((Z0c * M : ℕ) : ℝ) * ((B:ℝ) - 1) ^ m
          = (Z0c : ℝ) * ((M:ℝ) * ((B:ℝ) - 1) ^ m) := by push_cast; ring
        _ < (Z0c : ℝ) * (B:ℝ) ^ m := mul_lt_mul_of_pos_left h1 h2
    obtain ⟨D, hDX, hDcard, hDdom⟩ :=
      greedy_cover Xf (fun x y => x * y = y * x) B Z0c hB2 Inv hIsub hIcard
        (fun R hR hne => coset_pick F g B hB R hR hne) m Xf (Finset.Subset.refl _) hInvXf hlt
    have hD : ∀ x ∈ D, g⁻¹ * x ∈ F := by
      intro x hx
      have hx' := hDX hx
      rw [hXf, Finset.mem_filter] at hx'
      exact hx'.2
    have hdom : ∀ y : G, g⁻¹ * y ∈ F → ∃ x ∈ D, x * y = y * x := by
      intro y hy
      exact hDdom y (by rw [hXf, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hy⟩)
    have hcs := coset_cover_step F g D hD C a hCab hCcov hCcard hdom
    have htoNat : (aSet (g • (F : Set G))).toNat ≤ D.card * a := by
      have := ENat.toNat_le_toNat hcs (ENat.natCast_ne_top (D.card * a))
      simpa using this
    have hmle : (m : ℝ) ≤ (B:ℝ) * (1 + Real.log M) := by
      have hBR : (2:ℝ) ≤ (B:ℝ) := by exact_mod_cast hB2
      have h1 : ((⌈(B:ℝ) * Real.log M⌉₊ : ℕ) : ℝ) < (B:ℝ) * Real.log M + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      rw [hm]
      push_cast
      nlinarith
    calc ((aSet (g • (F : Set G))).toNat : ℝ) ≤ ((D.card * a : ℕ) : ℝ) := by exact_mod_cast htoNat
      _ ≤ (m : ℝ) * (a : ℝ) := by
          push_cast
          have hDm : (D.card : ℝ) ≤ (m : ℝ) := by exact_mod_cast hDcard
          nlinarith
      _ ≤ (B:ℝ) * (1 + Real.log M) * (a : ℝ) := by nlinarith


/-- Covering a finite group by finitely many cyclic subgroups shows `a(X) ≠ ⊤`. -/
theorem aSet_ne_top {G : Type} [Group G] [Finite G] (X : Set G) : aSet X ≠ ⊤ := by
  have := Fintype.ofFinite G
  have h : aSet X ≤ ((Finset.univ.image (fun x : G => Subgroup.zpowers x)).card : ℕ∞) := by
    refine iInf_le (fun C : {C : Finset (Subgroup G) //
      (∀ A ∈ C, ∀ x ∈ A, ∀ y ∈ A, Commute x y) ∧ ∀ g ∈ X, ∃ A ∈ C, g ∈ A} =>
      ((C : Finset (Subgroup G)).card : ℕ∞)) ⟨_, ?_, ?_⟩
    · intro A hA
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hA
      intro u hu v hv
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      exact zpow_mul_comm x m j
    · intro g _
      exact ⟨Subgroup.zpowers g, Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩,
        Subgroup.mem_zpowers g⟩
  intro htop
  rw [htop] at h
  exact (not_le.mpr (ENat.natCast_lt_top _)) h

/-- A finite group has a finite left transversal of any subgroup. -/
theorem exists_coset_transversal {G : Type} [Group G] [Finite G] (F : Subgroup G) :
    ∃ T : Finset G, T.card ≤ F.index ∧ ∀ x : G, ∃ g ∈ T, g⁻¹ * x ∈ F := by
  have := Fintype.ofFinite G
  have : Fintype (G ⧸ F) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : G ⧸ F => Quotient.out q), ?_, ?_⟩
  · refine le_trans Finset.card_image_le ?_
    rw [Finset.card_univ, Subgroup.index]
    exact le_of_eq (Nat.card_eq_fintype_card).symm
  · intro x
    refine ⟨Quotient.out (QuotientGroup.mk x : G ⧸ F),
      Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have h : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk x : G ⧸ F)) : G ⧸ F)
        = (QuotientGroup.mk x : G ⧸ F) := Quotient.out_eq _
    exact QuotientGroup.eq.mp h

/-- Assembling abelian covers of the cosets of `F` into an abelian cover of `G`. -/
theorem aG_le_of_coset_cover {G : Type} [Group G] [Finite G] (F : Subgroup G) (T : Finset G)
    (k : ℕ) (hT : ∀ x : G, ∃ g ∈ T, g⁻¹ * x ∈ F)
    (hk : ∀ g ∈ T, aSet (g • (F : Set G)) ≤ (k : ℕ∞)) :
    aG G ≤ ((T.card * k : ℕ) : ℕ∞) := by
  have hex : ∀ g ∈ T, ∃ C : Finset (Subgroup G),
      (∀ A ∈ C, ∀ x ∈ A, ∀ y ∈ A, Commute x y) ∧
      (∀ z ∈ g • (F : Set G), ∃ A ∈ C, z ∈ A) ∧ C.card ≤ k :=
    fun g hg => exists_cover_of_aSet_le _ k (hk g hg)
  choose! C hC1 hC2 hC3 using hex
  set D : Finset (Subgroup G) := T.biUnion C with hD
  have hDcard : D.card ≤ T.card * k := by
    refine le_trans Finset.card_biUnion_le ?_
    calc ∑ g ∈ T, (C g).card ≤ ∑ _g ∈ T, k := Finset.sum_le_sum (fun g hg => hC3 g hg)
      _ = T.card * k := by rw [Finset.sum_const, smul_eq_mul]
  refine le_trans (aG_le_of_cover D ⟨?_, ?_⟩) (by exact_mod_cast hDcard)
  · intro A hA
    obtain ⟨g, hg, hAg⟩ := Finset.mem_biUnion.mp hA
    exact hC1 g hg A hAg
  · intro x
    obtain ⟨g, hg, hx⟩ := hT x
    have hxmem : x ∈ g • (F : Set G) := ⟨g⁻¹ * x, hx, by simp [smul_eq_mul]⟩
    obtain ⟨A, hA, hxA⟩ := hC2 g hg x hxmem
    exact ⟨A, Finset.mem_biUnion.mpr ⟨g, hg, hA⟩, hxA⟩

/-- The polynomial estimate underlying Theorem 8.2. -/
theorem coset_reduction_numeric (n lm L0 : ℝ) (hn : 2 ≤ n) (hlm : 0 ≤ lm) (hL0 : 0 ≤ L0)
    (hlmn : lm ≤ n * L0) :
    n ^ 2 * ((2 * n + 1) ^ 2 * (1 + lm) + 1) ≤ 10 * (1 + L0) * n ^ 5 := by
  have hn0 : (0:ℝ) < n := by linarith
  have h1 : (2 * n + 1) ^ 2 ≤ 9 * n ^ 2 := by nlinarith
  have h2 : 1 + lm ≤ n * (1 + L0) := by nlinarith
  have h3 : (2 * n + 1) ^ 2 * (1 + lm) ≤ 9 * n ^ 2 * (n * (1 + L0)) := by
    have hp : (0:ℝ) ≤ 1 + lm := by linarith
    have hq : (0:ℝ) ≤ 9 * n ^ 2 := by positivity
    calc (2 * n + 1) ^ 2 * (1 + lm) ≤ (9 * n ^ 2) * (1 + lm) := mul_le_mul_of_nonneg_right h1 hp
      _ ≤ (9 * n ^ 2) * (n * (1 + L0)) := mul_le_mul_of_nonneg_left h2 hq
  have h4 : n ^ 2 ≤ n ^ 5 * (1 + L0) := by
    nlinarith [pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ n) (by norm_num : 2 ≤ 5)]
  nlinarith [h3, h4, sq_nonneg n]

/-- Turning a polynomial bound into a bound on the binary logarithm. -/
theorem logb_poly_bound (Y n K : ℝ) (hK : 1 ≤ K) (hn : 2 ≤ n) (hY : 0 < Y) (hYle : Y ≤ K * n ^ 5) :
    Real.logb 2 Y ≤ (Real.logb 2 K + 5) / Real.log 2 * Real.log n := by
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hn0 : (0:ℝ) < n := by linarith
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn
  have hKpos : (0:ℝ) < K := by linarith
  have h1 : Real.logb 2 Y ≤ Real.logb 2 (K * n ^ 5) :=
    Real.logb_le_logb_of_le (by norm_num) hY hYle
  have h2 : Real.logb 2 (K * n ^ 5) = Real.logb 2 K + 5 * (Real.log n / Real.log 2) := by
    rw [Real.logb_mul (by linarith) (by positivity), Real.logb_pow]
    simp [Real.logb]
  have hKb : 0 ≤ Real.logb 2 K := Real.logb_nonneg (by norm_num) hK
  have h3 : (1:ℝ) ≤ Real.log n / Real.log 2 := by
    rw [le_div_iff₀ hl2]; linarith
  have h4 : Real.logb 2 K ≤ Real.logb 2 K * (Real.log n / Real.log 2) := by nlinarith
  have h5 : (Real.logb 2 K + 5) / Real.log 2 * Real.log n
      = (Real.logb 2 K + 5) * (Real.log n / Real.log 2) := by field_simp
  rw [h5]
  linarith [h1, h2.le, h2.ge, h4]

/-- `log (n+2) ≥ 1` for `n ≥ 1`. -/
theorem one_le_log_add_two {n : ℕ} (hn : 1 ≤ n) : (1 : ℝ) ≤ Real.log ((n : ℝ) + 2) := by
  have hn0 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : Real.exp 1 ≤ (n : ℝ) + 2 := by
    have := Real.exp_one_lt_d9
    linarith
  have h2 := Real.log_le_log (Real.exp_pos 1) h1
  rwa [Real.log_exp] at h2

/-! ### The centralizer of the derived subgroup -/

/-- `H = C_G(G')`, the centralizer of the derived subgroup. -/
def centralizerDerived (G : Type) [Group G] : Subgroup G :=
  Subgroup.centralizer (commutator G : Set G)

instance centralizerDerived_normal (G : Type) [Group G] : (centralizerDerived G).Normal :=
  Subgroup.normal_centralizer

/-- First part of **Theorem 8.2**: `H' ≤ Z(H)` for `H = C_G(G')`, since `H'` lies in `G'` and
`H` centralizes `G'`. -/
theorem commutator_centralizerDerived_le_center (G : Type) [Group G] :
    commutator (centralizerDerived G) ≤ Subgroup.center (centralizerDerived G) := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [Subgroup.mem_center_iff]
  intro c
  have hab : ((⁅a, b⁆ : centralizerDerived G) : G) ∈ commutator G := by
    have h1 : ((⁅a, b⁆ : centralizerDerived G) : G) = ⁅(a : G), (b : G)⁆ := by
      simp [commutatorElement_def]
    rw [h1]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hc := (Subgroup.mem_centralizer_iff.mp c.2) _ hab
  exact Subtype.ext (by simpa using hc.symm)

/-- First part of **Theorem 8.2**: `H = C_G(G')` is nilpotent, of class at most two. -/
theorem centralizerDerived_isNilpotent (G : Type) [Group G] :
    Group.IsNilpotent (centralizerDerived G : Type _) := by
  refine ⟨2, ?_⟩
  rw [eq_top_iff]
  intro x _
  rw [Subgroup.mem_upperCentralSeries_succ_iff]
  intro y
  have hxy : ⁅x, y⁆ ∈ commutator (centralizerDerived G) :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
  have h2 := commutator_centralizerDerived_le_center G hxy
  rw [Subgroup.upperCentralSeries_one]
  simpa [commutatorElement_def] using h2

/-- A strictly smaller subgroup of a finite group has strictly smaller order. -/
theorem card_subgroup_lt_of_lt {A : Type} [Group A] [Finite A] {H K : Subgroup A} (h : H < K) :
    Nat.card H < Nat.card K := by
  have h2 : (H : Set A) ⊂ (K : Set A) := by exact_mod_cast h
  have h3 := Set.ncard_lt_ncard h2 (Set.toFinite _)
  rwa [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at h3

/-- Every subgroup `K` of a finite group is generated by a set `S` of elements with
`2^{|S|} ≤ |K|`: adjoining a generator at least doubles the order. -/
theorem exists_generating_finset_pow_le (A : Type) [Group A] [Finite A] :
    ∀ (n : ℕ) (K : Subgroup A), Nat.card K ≤ n →
      ∃ S : Finset A, Subgroup.closure (S : Set A) = K ∧ 2 ^ S.card ≤ Nat.card K := by
  have key : ∀ (x : A) (T : Set A),
      Subgroup.closure (insert x T) = Subgroup.closure ({x} : Set A) ⊔ Subgroup.closure T := by
    intro x T
    rw [Set.insert_eq, Subgroup.closure_union]
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K hK
    by_cases hbot : K = ⊥
    · subst hbot
      exact ⟨∅, by simp, by simp⟩
    · have hne : Nonempty {L : Subgroup A // L < K} := ⟨⟨⊥, lt_of_le_of_ne bot_le (Ne.symm hbot)⟩⟩
      obtain ⟨L0, hL0max⟩ := Finite.exists_max (fun L : {L : Subgroup A // L < K} => Nat.card L)
      obtain ⟨x, hxK, hxL⟩ : ∃ x ∈ K, x ∉ (L0 : Subgroup A) :=
        Set.exists_of_ssubset (by exact_mod_cast L0.2)
      set M : Subgroup A := Subgroup.closure (insert x (L0.1 : Set A)) with hM
      have hMle : M ≤ K := by
        rw [hM]
        exact Subgroup.closure_le _ |>.mpr (Set.insert_subset hxK (by exact_mod_cast L0.2.le))
      have hL0M : (L0 : Subgroup A) < M := by
        refine lt_of_le_of_ne (fun y hy => Subgroup.subset_closure (Set.mem_insert_of_mem _ hy)) ?_
        intro h
        exact hxL (h ▸ (Subgroup.subset_closure (Set.mem_insert _ _)))
      have hMK : M = K := by
        by_contra hMK
        have hlt : M < K := lt_of_le_of_ne hMle hMK
        have hmax := hL0max ⟨M, hlt⟩
        exact absurd (card_subgroup_lt_of_lt hL0M) (by simpa using not_lt.mpr hmax)
      have hcardlt : Nat.card (L0 : Subgroup A) < Nat.card K := card_subgroup_lt_of_lt L0.2
      obtain ⟨S0, hS0gen, hS0card⟩ := ih (Nat.card (L0 : Subgroup A)) (lt_of_lt_of_le hcardlt hK)
        L0.1 le_rfl
      refine ⟨insert x S0, ?_, ?_⟩
      · rw [← hMK, hM, Finset.coe_insert, key, key, hS0gen, Subgroup.closure_eq]
      · have hdvd : Nat.card (L0 : Subgroup A) ∣ Nat.card K := Subgroup.card_dvd_of_le L0.2.le
        have h2 : 2 * Nat.card (L0 : Subgroup A) ≤ Nat.card K := by
          obtain ⟨j, hj⟩ := hdvd
          have hpos : 0 < Nat.card (L0 : Subgroup A) := Nat.card_pos
          have hj2 : 2 ≤ j := by
            rcases Nat.lt_or_ge j 2 with h | h
            · interval_cases j <;> omega
            · exact h
          calc 2 * Nat.card (L0 : Subgroup A) ≤ j * Nat.card (L0 : Subgroup A) :=
                Nat.mul_le_mul_right _ hj2
            _ = Nat.card K := by rw [hj]; ring
        calc 2 ^ (insert x S0).card ≤ 2 ^ (S0.card + 1) :=
              Nat.pow_le_pow_right (by norm_num) (Finset.card_insert_le _ _)
          _ = 2 * 2 ^ S0.card := by ring
          _ ≤ 2 * Nat.card (L0 : Subgroup A) := Nat.mul_le_mul_left _ hS0card
          _ ≤ Nat.card K := h2

/-- A finite group of order `m` is generated by at most `log₂ m` elements. -/
theorem exists_generating_finset_top (A : Type) [Group A] [Finite A] :
    ∃ S : Finset A, Subgroup.closure (S : Set A) = ⊤ ∧ 2 ^ S.card ≤ Nat.card A := by
  obtain ⟨S, hgen, hcard⟩ :=
    exists_generating_finset_pow_le A (Nat.card (⊤ : Subgroup A)) ⊤ le_rfl
  exact ⟨S, hgen, by rwa [Subgroup.card_top] at hcard⟩

/-- An automorphism is determined by the images of a generating set. -/
theorem card_mulAut_le_pow {A : Type} [Group A] [Finite A] (S : Finset A)
    (hS : Subgroup.closure (S : Set A) = ⊤) :
    Nat.card (MulAut A) ≤ Nat.card A ^ S.card := by
  classical
  have hinj : Function.Injective (fun (f : MulAut A) (s : {x : A // x ∈ S}) => f (s : A)) := by
    intro f g hfg
    have heq : Set.EqOn (⇑(f.toMonoidHom)) (⇑(g.toMonoidHom)) (S : Set A) := by
      intro s hs
      exact congrFun hfg ⟨s, hs⟩
    have h2 := MonoidHom.eqOn_closure heq
    rw [hS] at h2
    ext a
    exact h2 (by simp)
  have hcard : Nat.card ({x : A // x ∈ S} → A) = Nat.card A ^ S.card := by
    rw [Nat.card_fun]
    congr 1
    simp
  calc Nat.card (MulAut A) ≤ Nat.card ({x : A // x ∈ S} → A) :=
        Nat.card_le_card_of_injective _ hinj
    _ = Nat.card A ^ S.card := hcard

/-- `|Aut(A)| ≤ |A|^{log₂ |A|}`, in logarithmic form. -/
theorem log2_card_mulAut_le (A : Type) [Group A] [Finite A] :
    Real.logb 2 (Nat.card (MulAut A)) ≤ (Real.logb 2 (Nat.card A)) ^ 2 := by
  obtain ⟨S, hSgen, hScard⟩ := exists_generating_finset_top A
  set t : ℝ := Real.logb 2 (Nat.card A) with ht
  have hA1 : 1 ≤ Nat.card A := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  have hAR : (1 : ℝ) ≤ (Nat.card A : ℝ) := by exact_mod_cast hA1
  have ht0 : 0 ≤ t := Real.logb_nonneg (by norm_num) hAR
  have hSt : (S.card : ℝ) ≤ t := by
    have h1 : ((2 : ℝ) ^ S.card) ≤ (Nat.card A : ℝ) := by exact_mod_cast hScard
    have h2 : Real.logb 2 ((2 : ℝ) ^ S.card) ≤ t :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity) h1
    simpa [Real.logb_pow, Real.logb_self_eq_one] using h2
  have hle : (Nat.card (MulAut A) : ℝ) ≤ (Nat.card A : ℝ) ^ S.card := by
    exact_mod_cast card_mulAut_le_pow S hSgen
  have hpos : (0 : ℝ) < (Nat.card (MulAut A) : ℝ) := by
    have h : 0 < Nat.card (MulAut A) := Nat.card_pos
    exact_mod_cast h
  calc Real.logb 2 (Nat.card (MulAut A))
      ≤ Real.logb 2 ((Nat.card A : ℝ) ^ S.card) :=
        Real.logb_le_logb_of_le (by norm_num) hpos hle
    _ = (S.card : ℝ) * t := by rw [Real.logb_pow]
    _ ≤ t * t := mul_le_mul_of_nonneg_right hSt ht0
    _ = t ^ 2 := by ring

/-- Conjugation embeds `G/C_G(H)` into `Aut(H)` for a normal subgroup `H`. -/
theorem index_centralizer_le_card_mulAut (G : Type) [Group G] [Finite G] (H : Subgroup G)
    [H.Normal] :
    (Subgroup.centralizer (H : Set G)).index ≤ Nat.card (MulAut H) := by
  have hker : (MulAut.conjNormal (G := G) (H := H)).ker = Subgroup.centralizer (H : Set G) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
    constructor
    · intro h y hy
      have h2 := congrArg (fun (f : MulAut H) => (f ⟨y, hy⟩ : G)) h
      simp only [MulAut.conjNormal_apply] at h2
      have h3 : g * y * g⁻¹ = y := by simpa using h2
      calc y * g = (g * y * g⁻¹) * g := by rw [h3]
        _ = g * y := by group
    · intro h
      ext y
      have hy := h y y.2
      simp only [MulAut.conjNormal_apply]
      show g * (y : G) * g⁻¹ = (y : G)
      rw [← hy]; group
  calc (Subgroup.centralizer (H : Set G)).index
      = Nat.card (MulAut.conjNormal (G := G) (H := H)).range := by
        rw [← hker, Subgroup.index_ker]
    _ ≤ Nat.card (MulAut H) := Nat.card_le_card_of_injective _ Subtype.val_injective

/-- The quasipolynomial index bound of **Theorem 8.2**: `log₂ [G : C_G(G')] = O((log(N+2))⁴)`. -/
theorem log2_index_centralizerDerived_le (hNVL : NeumannVaughanLeeBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (G : Type) [Group G] [Finite G] (N : ℕ), omegaG G ≤ (N : ℕ∞) →
      Real.logb 2 ((centralizerDerived G).index) ≤ C * (Real.logb 2 ((N : ℝ) + 2)) ^ 4 := by
  obtain ⟨C, hC, hcomm⟩ := log2_card_commutator_le hNVL
  refine ⟨C ^ 2, by positivity, ?_⟩
  intro G _ _ N hN
  have hidx : (centralizerDerived G).index ≤ Nat.card (MulAut (commutator G)) :=
    index_centralizer_le_card_mulAut G (commutator G)
  have hidx1 : 1 ≤ (centralizerDerived G).index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h1 : Real.logb 2 ((centralizerDerived G).index)
      ≤ Real.logb 2 (Nat.card (MulAut (commutator G))) := by
    refine Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hidx1) ?_
    exact_mod_cast hidx
  have h2 := log2_card_mulAut_le (commutator G : Type _)
  have hcm := hcomm G N hN
  have hcm0 : 0 ≤ Real.logb 2 (Nat.card (commutator G)) := by
    have h : (1 : ℝ) ≤ (Nat.card (commutator G) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
    exact Real.logb_nonneg (by norm_num) h
  have hsq : (Real.logb 2 (Nat.card (commutator G))) ^ 2
      ≤ (C * (Real.logb 2 ((N : ℝ) + 2)) ^ 2) ^ 2 := by
    apply pow_le_pow_left₀ hcm0 hcm
  have hexp : (C * (Real.logb 2 ((N : ℝ) + 2)) ^ 2) ^ 2
      = C ^ 2 * (Real.logb 2 ((N : ℝ) + 2)) ^ 4 := by ring
  linarith [h1, h2, hsq, hexp.le, hexp.ge]

/-- **Theorem 8.2** (Reduction to a nilpotent normal subgroup).  With `H = C_G(G')`, which is
nilpotent of class at most two by `centralizerDerived_isNilpotent`,
`log₂ a(G) ≤ log₂ a(H) + O((log(N+2))⁴)`. -/
theorem centralizer_derived_reduction (hPyber : PyberCentreIndex)
    (hNVL : NeumannVaughanLeeBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (G : Type) [Group G] [Finite G] (N : ℕ), 2 ≤ N → omegaG G = (N : ℕ∞) →
      log2a G ≤ log2a (centralizerDerived G : Type _) + C * (Real.log ((N : ℝ) + 2)) ^ 4 := by
  obtain ⟨C₀, hC₀1, hC₀⟩ := hPyber
  obtain ⟨C₄, hC₄, hidxb⟩ := log2_index_centralizerDerived_le hNVL
  have hL0 : 0 ≤ Real.log C₀ := Real.log_nonneg hC₀1
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set KK : ℝ := 10 * (1 + Real.log C₀) with hKK
  have hKK1 : 1 ≤ KK := by rw [hKK]; linarith
  have hKKb : 0 ≤ Real.logb 2 KK := Real.logb_nonneg (by norm_num) hKK1
  refine ⟨(Real.logb 2 KK + 5) / Real.log 2 + C₄ / (Real.log 2) ^ 4,
    add_pos (div_pos (by linarith) hl2) (div_pos hC₄ (by positivity)), ?_⟩
  intro G _ _ N hN2 hN
  have := Fintype.ofFinite G
  set H : Subgroup G := centralizerDerived G with hHdef
  set a : ℕ := (aG (H : Type _)).toNat with hadef
  have ha1 : 1 ≤ a := one_le_aG_toNat
  have haR : (1:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha1
  set B : ℕ := (2 * N + 1) ^ 2 with hBdef
  have hBidx : ∀ x : G, (Subgroup.centralizer ({x} : Set G)).index ≤ B :=
    fun x => conjClass_index_le N (le_of_eq hN) x
  set M : ℕ := ((H ⊓ Subgroup.center G).subgroupOf H).index with hMdef
  have hM1 : 1 ≤ M := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hMZ : M ≤ (Subgroup.center G).index := by
    rw [hMdef]
    have h0 : (H ⊓ Subgroup.center G).subgroupOf H = (Subgroup.center G).subgroupOf H :=
      Subgroup.inf_subgroupOf_left (Subgroup.center G) H
    rw [h0]
    have h6 := Subgroup.relIndex_le_of_le_right (H := Subgroup.center G) (K := H) (L := ⊤) le_top
      (by rw [Subgroup.relIndex_top_right]; exact Subgroup.index_ne_zero_of_finite)
    rwa [Subgroup.relIndex_top_right] at h6
  have hMR : (M:ℝ) ≤ C₀ ^ N :=
    le_trans (by exact_mod_cast hMZ) (hC₀ G N (le_of_eq hN))
  have hlm0 : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM1)
  have hlm : Real.log M ≤ (N:ℝ) * Real.log C₀ := by
    have h1 : Real.log M ≤ Real.log (C₀ ^ N) :=
      Real.log_le_log (by exact_mod_cast hM1) hMR
    rwa [Real.log_pow] at h1
  -- the size of one coset cover
  set k : ℕ := ⌈(B:ℝ) * (1 + Real.log M) * (a:ℝ)⌉₊ with hkdef
  have hcoset : ∀ g : G, aSet (g • (H : Set G)) ≤ (k : ℕ∞) := by
    intro g
    have h1 := coset_domination H g B M hBidx hMdef
    have h2 : (aSet (g • (H : Set G))).toNat ≤ k := by
      rw [hkdef]
      exact_mod_cast le_trans h1 (Nat.le_ceil _)
    have h3 : ((aSet (g • (H : Set G))).toNat : ℕ∞) = aSet (g • (H : Set G)) :=
      ENat.natCast_toNat (aSet_ne_top _)
    rw [← h3]
    exact_mod_cast h2
  obtain ⟨T, hTcard, hTcov⟩ := exists_coset_transversal H
  have hmain : aG G ≤ ((T.card * k : ℕ) : ℕ∞) :=
    aG_le_of_coset_cover H T k hTcov (fun g _ => hcoset g)
  have htoNat : (aG G).toNat ≤ T.card * k :=
    by simpa using ENat.toNat_le_toNat hmain (ENat.natCast_ne_top (T.card * k))
  -- numerical bookkeeping
  have hNR : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN2
  have hN1 : 1 ≤ N := by omega
  set Y : ℝ := (2 * (N:ℝ) + 1) ^ 2 * (1 + Real.log M) + 1 with hYdef
  have hYpos : 0 < Y := by
    rw [hYdef]
    nlinarith
  have hBR : ((B:ℕ) : ℝ) = (2 * (N:ℝ) + 1) ^ 2 := by rw [hBdef]; push_cast; ring
  have hkR0 : (k:ℝ) ≤ ((B:ℝ) * (1 + Real.log M) + 1) * (a:ℝ) := by
    have hB0 : (0:ℝ) ≤ (B:ℝ) := Nat.cast_nonneg _
    have ha0 : (0:ℝ) ≤ (a:ℝ) := Nat.cast_nonneg _
    have h1 : ((⌈(B:ℝ) * (1 + Real.log M) * (a:ℝ)⌉₊ : ℕ) : ℝ)
        < (B:ℝ) * (1 + Real.log M) * (a:ℝ) + 1 :=
      Nat.ceil_lt_add_one (mul_nonneg (mul_nonneg hB0 (by linarith)) ha0)
    rw [hkdef]
    nlinarith
  have hkR : (k:ℝ) ≤ Y * (a:ℝ) := by
    rw [hYdef]; rwa [hBR] at hkR0
  have hTidx : ((T.card : ℕ) : ℝ) ≤ (H.index : ℝ) := by exact_mod_cast hTcard
  have hidxpos : (0:ℝ) < (H.index : ℝ) := by
    have h : 0 < H.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    exact_mod_cast h
  have hprod : ((T.card * k : ℕ) : ℝ) ≤ (H.index : ℝ) * (Y * (a:ℝ)) := by
    have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg _
    calc ((T.card * k : ℕ) : ℝ) = ((T.card : ℕ) : ℝ) * (k:ℝ) := by push_cast; ring
      _ ≤ (H.index : ℝ) * (k:ℝ) := mul_le_mul_of_nonneg_right hTidx hk0
      _ ≤ (H.index : ℝ) * (Y * (a:ℝ)) := mul_le_mul_of_nonneg_left hkR hidxpos.le
  -- comparison of logarithms
  have hlogG : log2a G ≤ Real.logb 2 ((H.index : ℝ) * (Y * (a:ℝ))) := by
    have h1 : ((aG G).toNat : ℝ) ≤ (H.index : ℝ) * (Y * (a:ℝ)) :=
      le_trans (by exact_mod_cast htoNat) hprod
    have h2 : (0:ℝ) < ((aG G).toNat : ℝ) := by
      have h : 1 ≤ (aG G).toNat := one_le_aG_toNat
      exact_mod_cast h
    exact Real.logb_le_logb_of_le (by norm_num) h2 h1
  have hsplit : Real.logb 2 ((H.index : ℝ) * (Y * (a:ℝ)))
      = Real.logb 2 (H.index) + (Real.logb 2 Y + log2a (H : Type _)) := by
    rw [Real.logb_mul (ne_of_gt hidxpos) (by positivity),
      Real.logb_mul (ne_of_gt hYpos) (by positivity)]
    rfl
  have hYle : Y ≤ KK * (N:ℝ) ^ 5 := by
    have hnum := coset_reduction_numeric (N:ℝ) (Real.log M) (Real.log C₀) hNR hlm0 hL0 hlm
    have hN2' : (1:ℝ) ≤ (N:ℝ) ^ 2 := by nlinarith
    have : Y ≤ (N:ℝ) ^ 2 * Y := by nlinarith
    rw [hKK]
    calc Y ≤ (N:ℝ) ^ 2 * Y := this
      _ = (N:ℝ) ^ 2 * ((2 * (N:ℝ) + 1) ^ 2 * (1 + Real.log M) + 1) := by rw [hYdef]
      _ ≤ 10 * (1 + Real.log C₀) * (N:ℝ) ^ 5 := hnum
  have hlast : Real.logb 2 Y ≤ (Real.logb 2 KK + 5) / Real.log 2 * Real.log N :=
    logb_poly_bound Y (N:ℝ) KK hKK1 hNR hYpos hYle
  -- the quasipolynomial index term
  have hidxlog : Real.logb 2 (H.index) ≤ C₄ / (Real.log 2) ^ 4 * (Real.log ((N:ℝ) + 2)) ^ 4 := by
    have h1 := hidxb G N (le_of_eq hN)
    have h2 : (Real.logb 2 ((N : ℝ) + 2)) ^ 4
        = (Real.log ((N:ℝ) + 2)) ^ 4 / (Real.log 2) ^ 4 := by
      rw [Real.logb, div_pow]
    rw [h2] at h1
    calc Real.logb 2 (H.index) ≤ C₄ * ((Real.log ((N:ℝ) + 2)) ^ 4 / (Real.log 2) ^ 4) := h1
      _ = C₄ / (Real.log 2) ^ 4 * (Real.log ((N:ℝ) + 2)) ^ 4 := by ring
  -- the polynomial coset term
  have hlogt : (1:ℝ) ≤ Real.log ((N:ℝ) + 2) := one_le_log_add_two hN1
  have hlogN : Real.log N ≤ (Real.log ((N:ℝ) + 2)) ^ 4 := by
    have h1 : Real.log N ≤ Real.log ((N:ℝ) + 2) :=
      Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log ((N:ℝ) + 2) ≤ (Real.log ((N:ℝ) + 2)) ^ 4 := by
      calc Real.log ((N:ℝ) + 2) = (Real.log ((N:ℝ) + 2)) ^ 1 := (pow_one _).symm
        _ ≤ (Real.log ((N:ℝ) + 2)) ^ 4 := pow_le_pow_right₀ hlogt (by norm_num)
    linarith
  have hcoeff : (0:ℝ) ≤ (Real.logb 2 KK + 5) / Real.log 2 := by positivity
  nlinarith [hlogG, hsplit.le, hsplit.ge, hlast, hidxlog, hlogN, hcoeff]

/-! ## 9. Completion of the proof -/

/-- `ω` does not increase when passing to a subgroup. -/
theorem omegaG_subgroup_le {G : Type} [Group G] (H : Subgroup G) : omegaG H ≤ omegaG G := by
  classical
  refine iSup_le ?_
  rintro ⟨S, hS⟩
  have hinj : Function.Injective (fun x : H => (x : G)) := Subtype.val_injective
  have hnc : IsNoncommSet ((S.image (fun x : H => (x : G)) : Finset G) : Set G) := by
    intro x hx y hy hxy hcomm
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have hab : a ≠ b := fun h => hxy (by rw [h])
    refine hS ha hb hab ?_
    exact Subtype.ext hcomm
  have h2 := card_le_omegaG (S.image (fun x : H => (x : G))) hnc
  rwa [Finset.card_image_of_injective _ hinj] at h2

/-- `1 ≤ √n` for `n ≥ 1`. -/
theorem one_le_sqrt_nat {n : ℕ} (hn : 1 ≤ n) : (1 : ℝ) ≤ Real.sqrt n := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt hnR

/-- The error profile is at least `1` for `n ≥ 1`. -/
theorem one_le_sqrt_mul_log_cube {n : ℕ} (hn : 1 ≤ n) :
    (1 : ℝ) ≤ Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3 := by
  have hsn := one_le_sqrt_nat hn
  have hlogn := one_le_log_add_two hn
  have hL3 : (1 : ℝ) ≤ (Real.log ((n : ℝ) + 2)) ^ 3 := one_le_pow₀ hlogn
  nlinarith [mul_nonneg (sub_nonneg.mpr hsn) (sub_nonneg.mpr hL3)]

/-- Monotonicity of the error profile `n ↦ n/2 + C √n (log (n+2))³`. -/
theorem sqrt_log_cube_mono {C : ℝ} (hC : 0 ≤ C) {m n : ℕ} (h : m ≤ n) :
    C * Real.sqrt m * (Real.log ((m : ℝ) + 2)) ^ 3
      ≤ C * Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3 := by
  have hmn : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
  have hs : Real.sqrt m ≤ Real.sqrt n := Real.sqrt_le_sqrt hmn
  have hlm : 0 ≤ Real.log ((m : ℝ) + 2) :=
    Real.log_nonneg (by have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg _; linarith)
  have hl : Real.log ((m : ℝ) + 2) ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log (by have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg _; linarith) (by linarith)
  have hcube : (Real.log ((m : ℝ) + 2)) ^ 3 ≤ (Real.log ((n : ℝ) + 2)) ^ 3 :=
    pow_le_pow_left₀ hlm hl 3
  have h1 : C * Real.sqrt m ≤ C * Real.sqrt n := mul_le_mul_of_nonneg_left hs hC
  have h2 : 0 ≤ C * Real.sqrt m := mul_nonneg hC (Real.sqrt_nonneg _)
  have h3 : 0 ≤ (Real.log ((m : ℝ) + 2)) ^ 3 := pow_nonneg hlm 3
  calc C * Real.sqrt m * (Real.log ((m : ℝ) + 2)) ^ 3
      ≤ C * Real.sqrt m * (Real.log ((n : ℝ) + 2)) ^ 3 := mul_le_mul_of_nonneg_left hcube h2
    _ ≤ C * Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3 :=
        mul_le_mul_of_nonneg_right h1 (pow_nonneg (le_trans hlm hl) 3)

/-- `log((N+2))⁴ ≤ 4 √n (log(n+2))³` for `N ≤ n`: the quasipolynomial extension cost of
Theorem 8.2 is absorbed by the error term of the main theorem. -/
theorem log_pow_four_le_sqrt_log_cube {N n : ℕ} (hn : 1 ≤ n) (hNn : N ≤ n) :
    (Real.log ((N : ℝ) + 2)) ^ 4 ≤ 4 * (Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hNR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
  have hs : Real.sqrt ((n : ℝ) + 2) ≤ 2 * Real.sqrt n := by
    have h1 : Real.sqrt ((n : ℝ) + 2) ≤ Real.sqrt (4 * (n : ℝ)) :=
      Real.sqrt_le_sqrt (by linarith)
    have h2 : Real.sqrt (4 * (n : ℝ)) = 2 * Real.sqrt n := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by norm_num)]
    linarith [h1, h2.le, h2.ge]
  have hlogsqrt : Real.log ((n : ℝ) + 2) ≤ 4 * Real.sqrt n := by
    have h0 : (0 : ℝ) < Real.sqrt ((n : ℝ) + 2) := Real.sqrt_pos.mpr (by linarith)
    have h1 : Real.log (Real.sqrt ((n : ℝ) + 2)) ≤ Real.sqrt ((n : ℝ) + 2) - 1 :=
      Real.log_le_sub_one_of_pos h0
    have h2 : Real.log (Real.sqrt ((n : ℝ) + 2)) = Real.log ((n : ℝ) + 2) / 2 :=
      Real.log_sqrt (by linarith)
    rw [h2] at h1
    linarith
  have hle : Real.log ((N : ℝ) + 2) ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have h1 : (1 : ℝ) ≤ Real.log ((n : ℝ) + 2) := one_le_log_add_two hn
  have h0 : (0 : ℝ) ≤ Real.log ((N : ℝ) + 2) :=
    Real.log_nonneg (by have : (0:ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N; linarith)
  have hpow : (Real.log ((N : ℝ) + 2)) ^ 4 ≤ (Real.log ((n : ℝ) + 2)) ^ 4 :=
    pow_le_pow_left₀ h0 hle 4
  have hcube : (0 : ℝ) ≤ (Real.log ((n : ℝ) + 2)) ^ 3 := by positivity
  nlinarith [hpow, hlogsqrt, hcube]

/-- The uniform upper bound for finite groups: combining the reduction to `C_G(G')`
(Theorem 8.2) with the nilpotent bound (Theorem 7.1). -/
theorem log2a_upper_uniform (hPyber : PyberCentreIndex) (hNVL : NeumannVaughanLeeBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (G : Type) [Group G] [Finite G] (n : ℕ), 1 ≤ n → omegaG G ≤ (n : ℕ∞) →
      log2a G ≤ (n : ℝ) / 2 + C * Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3 := by
  classical
  obtain ⟨C₂, hC₂, hfr⟩ := centralizer_derived_reduction hPyber hNVL
  obtain ⟨C₃, hC₃, hnil⟩ := nilpotent_sqrt_bound hNVL
  refine ⟨4 * C₂ + C₃, by linarith, ?_⟩
  intro G _ _ n hn1 hn
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hsn := one_le_sqrt_nat hn1
  have hlogn : (0 : ℝ) ≤ Real.log ((n : ℝ) + 2) := le_trans zero_le_one (one_le_log_add_two hn1)
  have herr : (0 : ℝ) ≤ Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3 :=
    mul_nonneg (by linarith) (pow_nonneg hlogn 3)
  by_cases habel : ∀ x y : G, Commute x y
  · have h0 : log2a G = 0 := log2a_eq_zero_of_abelian habel
    rw [h0]
    nlinarith [herr, hC₂, hC₃]
  · set N : ℕ := (omegaG G).toNat with hNdef
    have hNeq : omegaG G = (N : ℕ∞) := (ENat.natCast_toNat omegaG_ne_top).symm
    have hN3 : 3 ≤ N := by
      have h1 := three_le_omegaG_of_nonabelian habel
      rw [hNeq] at h1
      exact_mod_cast h1
    have hNn : N ≤ n := by
      have h1 : (N : ℕ∞) ≤ (n : ℕ∞) := by rw [← hNeq]; exact hn
      exact_mod_cast h1
    have hstep1 := hfr G N (by omega) hNeq
    -- the centralizer of the derived subgroup
    have : Group.IsNilpotent (centralizerDerived G : Type _) := centralizerDerived_isNilpotent G
    set m : ℕ := (omegaG (centralizerDerived G : Type _)).toNat with hmdef
    have hmeq : omegaG (centralizerDerived G : Type _) = (m : ℕ∞) :=
      (ENat.natCast_toNat omegaG_ne_top).symm
    have hmN : m ≤ N := by
      have h1 : (m : ℕ∞) ≤ (N : ℕ∞) := by
        rw [← hmeq, ← hNeq]; exact omegaG_subgroup_le _
      exact_mod_cast h1
    have hstep2 := (hnil (centralizerDerived G : Type _) m (centralizerDerived_isNilpotent G)
      hmeq).1
    -- numerical assembly
    have hmn : m ≤ n := le_trans hmN hNn
    have hmR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have hA : C₃ * Real.sqrt m * (Real.log ((m : ℝ) + 2)) ^ 3
        ≤ C₃ * Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3 :=
      sqrt_log_cube_mono hC₃.le hmn
    have hB : (Real.log ((N : ℝ) + 2)) ^ 4
        ≤ 4 * (Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3) :=
      log_pow_four_le_sqrt_log_cube hn1 hNn
    have hD : C₂ * (Real.log ((N : ℝ) + 2)) ^ 4
        ≤ C₂ * (4 * (Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3)) :=
      mul_le_mul_of_nonneg_left hB hC₂.le
    nlinarith [hstep1, hstep2, hA, hD, hmR]

/-- `h(0) = 0`: no group has an empty noncommuting set as its largest one. -/
theorem hFun_zero : hFun 0 = 0 := by
  unfold hFun
  have hempty : {a : ℕ∞ | ∃ (G : Type) (inst : Group G),
      @omegaG G inst ≤ ((0 : ℕ) : ℕ∞) ∧ @aG G inst = a} = ∅ := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨G, inst, hom, -⟩
    have h1 : (1 : ℕ∞) ≤ (0 : ℕ∞) :=
      le_trans (@one_le_omegaG G inst) (by simpa using hom)
    simp at h1
  rw [hempty, sSup_empty]
  rfl

/-- `log₂ h(0) = 0`. -/
theorem log2h_zero : log2h 0 = 0 := by
  unfold log2h
  rw [hFun_zero]
  simp

/-- The upper half of Theorem 2.2: `h(n)` is finite and `log₂ h(n) ≤ n/2 + O(√n (log (n+2))³)`. -/
theorem log2h_upper (hNeu : NeumannCentreQuotientFinite) (hSchur : SchurDerivedFinite)
    (hHall : HallStemTheorem) (hPyber : PyberCentreIndex) (hNVL : NeumannVaughanLeeBound)
    :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → hFun n ≠ ⊤ ∧
      log2h n ≤ (n : ℝ) / 2 + C * Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3 := by
  classical
  obtain ⟨C₁, hC₁, hub⟩ := log2a_upper_uniform hPyber hNVL
  refine ⟨C₁ + 1, by linarith, ?_⟩
  intro n hn1
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hsn := one_le_sqrt_nat hn1
  have hlogn := one_le_log_add_two hn1
  have herr := one_le_sqrt_mul_log_cube hn1
  set E : ℝ := (n : ℝ) / 2 + C₁ * Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3 with hE
  have hE0 : 0 ≤ E := by
    rw [hE]
    nlinarith [herr, hC₁, hnR]
  set k : ℕ := ⌈E⌉₊ with hk
  have hEk : E ≤ (k : ℝ) := Nat.le_ceil E
  have hkE : (k : ℝ) ≤ E + 1 := by
    rw [hk]
    exact le_of_lt (Nat.ceil_lt_add_one hE0)
  have hle : hFun n ≤ ((2 ^ k : ℕ) : ℕ∞) := by
    rw [hFun_eq_sup_finite hNeu hSchur hHall n]
    apply sSup_le
    rintro a ⟨H, instH, hfin, hom, rfl⟩
    have hlog : @log2a H instH ≤ E := hub H n hn1 hom
    have hpos : (0 : ℝ) < ((@aG H instH).toNat : ℝ) := by
      have : 1 ≤ (@aG H instH).toNat := one_le_aG_toNat
      exact_mod_cast this
    have hrp : ((@aG H instH).toNat : ℝ) ≤ (2 : ℝ) ^ k := by
      have h1 : ((@aG H instH).toNat : ℝ)
          = (2 : ℝ) ^ (Real.logb 2 ((@aG H instH).toNat : ℝ)) :=
        (Real.rpow_logb (by norm_num) (by norm_num) hpos).symm
      have h2 : Real.logb 2 ((@aG H instH).toNat : ℝ) ≤ (k : ℝ) := le_trans hlog hEk
      have h3 : (2 : ℝ) ^ (Real.logb 2 ((@aG H instH).toNat : ℝ)) ≤ (2 : ℝ) ^ ((k : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
      rw [Real.rpow_natCast] at h3
      rw [h1]; exact h3
    have h4 : (@aG H instH).toNat ≤ 2 ^ k := by
      have : (((@aG H instH).toNat : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by push_cast; exact hrp
      exact_mod_cast this
    calc @aG H instH = (((@aG H instH).toNat : ℕ) : ℕ∞) := (ENat.natCast_toNat aG_ne_top).symm
      _ ≤ ((2 ^ k : ℕ) : ℕ∞) := by exact_mod_cast h4
  have hne : hFun n ≠ ⊤ := by
    intro htop
    rw [htop] at hle
    exact (not_le.mpr (ENat.natCast_lt_top _)) hle
  refine ⟨hne, ?_⟩
  have htoNat : (hFun n).toNat ≤ 2 ^ k := by
    have := ENat.toNat_le_toNat hle (ENat.natCast_ne_top _)
    rwa [ENat.toNat_natCast] at this
  have hlogh : log2h n ≤ (k : ℝ) := by
    unfold log2h
    rcases Nat.eq_zero_or_pos ((hFun n).toNat) with h0 | h0
    · rw [h0]
      simp only [Nat.cast_zero, Real.logb_zero]
      exact Nat.cast_nonneg k
    · have h1 : (((hFun n).toNat : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast htoNat
      have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num)
        (by exact_mod_cast h0 : (0:ℝ) < (((hFun n).toNat : ℕ) : ℝ)) h1
      refine le_trans h2 (le_of_eq ?_)
      rw [show (((2 ^ k : ℕ)) : ℝ) = (2:ℝ) ^ k by push_cast; ring]
      simp [Real.logb_pow, Real.logb_self_eq_one]
  have : (k : ℝ) ≤ (n : ℝ) / 2 + (C₁ + 1) * Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3 := by
    refine le_trans hkE ?_
    rw [hE]
    nlinarith [herr]
  linarith

/-- **Theorem 2.2** (Main theorem): `log₂ h(n) = n/2 + O(√n (log (n+2))³)`. -/
theorem main_theorem (hNeu : NeumannCentreQuotientFinite) (hSchur : SchurDerivedFinite)
    (hHall : HallStemTheorem) (hPyber : PyberCentreIndex) (hNVL : NeumannVaughanLeeBound)
    (hE : ExtraspecialExists) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      |log2h n - (n : ℝ) / 2| ≤ C * Real.sqrt n * (Real.log (n + 2)) ^ 3 := by
  obtain ⟨C₁, hC₁, hup⟩ := log2h_upper hNeu hSchur hHall hPyber hNVL
  obtain ⟨C₀, hlow⟩ := log2h_lower hE
  refine ⟨C₁ + |C₀| + 1, by positivity, ?_⟩
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · simp [log2h_zero]
  · have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hsn := one_le_sqrt_nat hn1
    have hlogn := one_le_log_add_two hn1
    have herr := one_le_sqrt_mul_log_cube hn1
    set W : ℝ := Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3 with hW
    obtain ⟨hne, hupn⟩ := hup n hn1
    have hupn' : log2h n ≤ (n : ℝ) / 2 + C₁ * W := by
      rw [hW]; linarith [hupn]
    have hlown := hlow n hne
    have hC0 : C₀ ≤ |C₀| := le_abs_self C₀
    have hC0' : 0 ≤ |C₀| := abs_nonneg C₀
    have hgoal : (C₁ + |C₀| + 1) * Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3
        = (C₁ + |C₀| + 1) * W := by rw [hW]; ring
    rw [hgoal, abs_le]
    constructor
    · nlinarith [herr, hlown, hC0, hC₁, hC0']
    · nlinarith [herr, hupn', hC₁, hC0']

open Filter Topology in
/-- **Theorem 2.2**, consequence: `h(n)^{1/n} → √2`. -/
theorem hFun_root_tendsto (hNeu : NeumannCentreQuotientFinite) (hSchur : SchurDerivedFinite)
    (hHall : HallStemTheorem) (hPyber : PyberCentreIndex) (hNVL : NeumannVaughanLeeBound)
    (hE : ExtraspecialExists) :
    Filter.Tendsto (fun n : ℕ => (((hFun n).toNat : ℝ)) ^ ((1 : ℝ) / n)) Filter.atTop
      (nhds (Real.sqrt 2)) := by
  obtain ⟨C, hC, hbound⟩ := main_theorem hNeu hSchur hHall hPyber hNVL hE
  set T : ℕ → ℕ := fun n => (hFun n).toNat with hT_def
  have hL : ∀ n, log2h n = Real.logb 2 (T n) := fun n => rfl
  have hg : Tendsto (fun n : ℕ => C * ((Real.log (n + 2)) ^ 3 / Real.sqrt n)) atTop (𝓝 0) := by
    simpa using log_cube_div_sqrt_tendsto.const_mul C
  have hkey0 : Tendsto (fun n : ℕ => log2h n / n - 1/2) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hn0 : (0:ℝ) < n := by linarith
    have hs : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn0
    have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
    have heq : log2h n / n - 1/2 = (log2h n - (n:ℝ)/2) / n := by field_simp
    rw [heq, Real.norm_eq_abs, abs_div, abs_of_pos hn0, div_le_iff₀ hn0]
    calc |log2h n - (n:ℝ)/2| ≤ C * Real.sqrt n * (Real.log (n+2))^3 := hbound n
      _ = C * ((Real.log (n + 2)) ^ 3 / Real.sqrt n) * n := by
          field_simp
          linear_combination (Real.log ((n:ℝ)+2)^3) * hsq
  have hkey : Tendsto (fun n : ℕ => log2h n / n) atTop (𝓝 (1/2)) := by
    have := hkey0.add_const (1/2)
    simpa using this
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < T n := by
    have h4 : ∀ᶠ n : ℕ in atTop, log2h n / n ∈ Set.Ioi (1/4 : ℝ) :=
      hkey (Ioi_mem_nhds (by norm_num))
    filter_upwards [h4] with n hn
    rcases Nat.eq_zero_or_pos (T n) with h | h
    · exfalso
      rw [hL, h] at hn
      simp [Real.logb] at hn
      exact absurd hn (by norm_num)
    · exact h
  refine Tendsto.congr' ?_
    (?_ : Tendsto (fun n : ℕ => Real.exp (Real.log 2 * (log2h n / n))) atTop _)
  · filter_upwards [hpos, eventually_ge_atTop 1] with n hn hn1
    have hTn : (0:ℝ) < (T n : ℝ) := by exact_mod_cast hn
    have hn0 : (0:ℝ) < n := by
      have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
      linarith
    rw [Real.rpow_def_of_pos hTn, hL, Real.logb]
    congr 1
    field_simp [Real.log_ne_zero_of_pos_of_ne_one]
  · have h2 : Real.exp (Real.log 2 * (1/2)) = Real.sqrt 2 := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num)]
    rw [← h2]
    exact (Real.continuous_exp.tendsto _).comp (tendsto_const_nhds.mul hkey)

/-! ## 10. Immediate consequences -/

/-- `ι(G)`: the least index of an abelian subgroup of finite index. -/
noncomputable def iotaG (G : Type) [Group G] : ℕ∞ :=
  ⨅ A : {A : Subgroup G // (∀ x ∈ A, ∀ y ∈ A, Commute x y) ∧ 0 < A.index},
    (((A : Subgroup G).index : ℕ∞))

/-- `i(n) = sup { ι(G) : ω(G) ≤ n }`. -/
noncomputable def iFun (n : ℕ) : ℕ∞ :=
  sSup {a : ℕ∞ | ∃ (G : Type) (inst : Group G), @omegaG G inst ≤ (n : ℕ∞) ∧ @iotaG G inst = a}

/-- `log₂ i(n)`. -/
noncomputable def log2i (n : ℕ) : ℝ := Real.logb 2 ((iFun n).toNat)

/-- First step of Corollary 10.1: by Neumann's covering lemma an abelian cover of a finite group
`G` by `a(G)` subgroups contains an abelian subgroup of index at most `a(G)`, so
`ι(G) ≤ a(G)`. -/
theorem iotaG_le_aG (hNC : NeumannCoveringLemma) (G : Type) [Group G] :
    iotaG G ≤ aG G := by
  refine le_iInf ?_
  rintro ⟨C, hC⟩
  obtain ⟨A, hA, hpos, hidx⟩ := hNC G C.card C rfl hC.2
  calc iotaG G ≤ ((A.index : ℕ) : ℕ∞) :=
        iInf_le (fun B : {B : Subgroup G // (∀ x ∈ B, ∀ y ∈ B, Commute x y) ∧ 0 < B.index} =>
          (((B : Subgroup G).index : ℕ∞))) ⟨A, hC.1 A hA, hpos⟩
    _ ≤ ((C.card : ℕ) : ℕ∞) := by exact_mod_cast hidx

/-- In extraspecial data the projection sends `1` to `0`. -/
theorem extraspecial_pi_one {m : ℕ} {E : Type} [Group E] (D : ExtraspecialData m E) :
    D.pi 1 = 0 := by
  have h := (D.pi_mul 1 1).symm
  simp only [mul_one] at h
  simpa using h

/-- The projection of extraspecial data, packaged as a group homomorphism onto the symplectic
space (written multiplicatively). -/
def piHom {m : ℕ} {E : Type} [Group E] (D : ExtraspecialData m E) :
    E →* Multiplicative (Fin m → ZMod 2 × ZMod 2) where
  toFun := fun x => Multiplicative.ofAdd (D.pi x)
  map_one' := by simp [extraspecial_pi_one D]
  map_mul' := fun x y => congrArg Multiplicative.ofAdd (D.pi_mul x y)

theorem piHom_apply {m : ℕ} {E : Type} [Group E] (D : ExtraspecialData m E) (x : E) :
    piHom D x = Multiplicative.ofAdd (D.pi x) := rfl

theorem piHom_ker {m : ℕ} {E : Type} [Group E] (D : ExtraspecialData m E) :
    (piHom D).ker = Subgroup.center E := by
  ext x
  rw [MonoidHom.mem_ker, piHom_apply, ← D.pi_ker]
  exact ⟨fun h => by simpa using congrArg Multiplicative.toAdd h,
    fun h => by rw [h]; rfl⟩

theorem piHom_surjective {m : ℕ} {E : Type} [Group E] (D : ExtraspecialData m E) :
    Function.Surjective (piHom D) := by
  intro v
  obtain ⟨x, hx⟩ := D.pi_surj (Multiplicative.toAdd v)
  exact ⟨x, by rw [piHom_apply, hx]; rfl⟩

/-- An extraspecial `2`-group of type `m` has order `2^{1+2m}`. -/
theorem extraspecial_card {m : ℕ} {E : Type} [Group E] [Finite E]
    (D : ExtraspecialData m E) : Nat.card E = 2 * 4 ^ m := by
  have hV : Nat.card (Multiplicative (Fin m → ZMod 2 × ZMod 2)) = 4 ^ m := by
    simp [Nat.card_eq_fintype_card]
  have hidx : (Subgroup.center E).index = 4 ^ m := by
    rw [← piHom_ker D, Subgroup.index,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
        (piHom D) (piHom_surjective D)).toEquiv]
    exact hV
  have h := Subgroup.card_mul_index (Subgroup.center E)
  rw [D.card_center, hidx] at h
  exact h.symm

/-- The image of an abelian subgroup of an extraspecial `2`-group in the symplectic quotient is
an isotropic subspace, so it has at most `2^m` elements. -/
theorem exists_isotropic_of_abelian {m : ℕ} {E : Type} [Group E] (D : ExtraspecialData m E)
    (A : Subgroup E) (hA : ∀ x ∈ A, ∀ y ∈ A, Commute x y) :
    ∃ W : Submodule (ZMod 2) (Fin m → ZMod 2 × ZMod 2),
      (∀ v, v ∈ W ↔ ∃ x ∈ A, D.pi x = v) ∧ Nat.card W ≤ 2 ^ m := by
  have hpi1 := extraspecial_pi_one D
  have hz2 : ∀ d : ZMod 2, d = 0 ∨ d = 1 := by decide
  refine ⟨{ carrier := {v | ∃ x ∈ A, D.pi x = v}
            add_mem' := ?_
            zero_mem' := ⟨1, A.one_mem, hpi1⟩
            smul_mem' := ?_ }, fun v => Iff.rfl, ?_⟩
  · rintro a b ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, A.mul_mem hx hy, D.pi_mul x y⟩
  · rintro c a ⟨x, hx, rfl⟩
    rcases hz2 c with rfl | rfl
    · exact ⟨1, A.one_mem, by simp [hpi1]⟩
    · exact ⟨x, hx, by simp⟩
  · refine isotropic_card_le m _ ?_
    rintro u ⟨x, hx, rfl⟩ v ⟨y, hy, rfl⟩
    exact (D.comm_iff x y).mp (commutatorElement_eq_one_iff_commute.mpr (hA x hx y hy))

/-- An abelian subgroup of an extraspecial `2`-group of type `m` has order at most `2^{m+1}`. -/
theorem extraspecial_abelian_card_le {m : ℕ} {E : Type} [Group E] [Finite E]
    (D : ExtraspecialData m E) (A : Subgroup E) (hA : ∀ x ∈ A, ∀ y ∈ A, Commute x y) :
    Nat.card A ≤ 2 * 2 ^ m := by
  classical
  obtain ⟨W, hW, hWcard⟩ := exists_isotropic_of_abelian D A hA
  set g : A →* Multiplicative (Fin m → ZMod 2 × ZMod 2) := (piHom D).comp A.subtype with hg
  have hker : Nat.card g.ker ≤ 2 := by
    have hinj : Function.Injective
        (fun z : g.ker => (⟨(z : A), by
          have hz : (piHom D) ((z : A) : E) = 1 := z.2
          have : ((z : A) : E) ∈ (piHom D).ker := hz
          rwa [piHom_ker D] at this⟩ : Subgroup.center E)) := by
      intro z₁ z₂ h
      have h2 := congrArg (fun t : Subgroup.center E => (t : E)) h
      exact Subtype.ext (Subtype.ext h2)
    exact le_trans (Nat.card_le_card_of_injective _ hinj) (le_of_eq D.card_center)
  have hrange : Nat.card g.range ≤ 2 ^ m := by
    have hinj : Function.Injective
        (fun w : g.range => (⟨Multiplicative.toAdd (w : Multiplicative _), by
          obtain ⟨z, hz⟩ := w.2
          refine (hW _).mpr ⟨(z : E), z.2, ?_⟩
          rw [← hz]
          rfl⟩ : W)) := by
      intro w₁ w₂ h
      have h2 := congrArg (fun t : W => (t : Fin m → ZMod 2 × ZMod 2)) h
      exact Subtype.ext (Multiplicative.toAdd.injective h2)
    exact le_trans (Nat.card_le_card_of_injective _ hinj) hWcard
  have hidx : g.ker.index = Nat.card g.range := by
    rw [Subgroup.index]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv
  have hcard := Subgroup.card_mul_index g.ker
  rw [hidx] at hcard
  calc Nat.card A = Nat.card g.ker * Nat.card g.range := hcard.symm
    _ ≤ 2 * 2 ^ m := Nat.mul_le_mul hker hrange

/-- **Corollary 10.1**, lower bound input: every abelian subgroup of an extraspecial `2`-group of
type `m` has index at least `2^m`. -/
theorem extraspecial_iota_lower {m : ℕ} {E : Type} [Group E] [Finite E]
    (D : ExtraspecialData m E) : ((2 ^ m : ℕ) : ℕ∞) ≤ iotaG E := by
  refine le_iInf ?_
  rintro ⟨A, hAc, hApos⟩
  have hcard := extraspecial_abelian_card_le D A hAc
  have hmul := Subgroup.index_mul_card A
  have hEcard := extraspecial_card D
  have h4 : (4 : ℕ) ^ m = 2 ^ m * 2 ^ m := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
  have h1 : 2 ^ m * (2 * 2 ^ m) ≤ A.index * (2 * 2 ^ m) := by
    calc 2 ^ m * (2 * 2 ^ m) = 2 * 4 ^ m := by rw [h4]; ring
      _ = A.index * Nat.card A := by rw [hmul, hEcard]
      _ ≤ A.index * (2 * 2 ^ m) := Nat.mul_le_mul_left _ hcard
  have hpos : 0 < 2 * 2 ^ m := by positivity
  exact_mod_cast Nat.le_of_mul_le_mul_right h1 hpos

/-- The extraspecial groups force `i(n) ≥ 2^m` whenever `2m + 1 ≤ n`. -/
theorem iFun_ge_extraspecial (hE : ExtraspecialExists) (m n : ℕ) (hmn : 2 * m + 1 ≤ n) :
    ((2 ^ m : ℕ) : ℕ∞) ≤ iFun n := by
  obtain ⟨E, inst, hfin, ⟨D⟩⟩ := hE m
  refine le_trans (@extraspecial_iota_lower m E inst hfin D) (le_sSup ⟨E, inst, ?_, rfl⟩)
  rw [@extraspecial_omega m E inst D]
  exact_mod_cast hmn

/-- `i(n) ≤ h(n)`. -/
theorem iFun_le_hFun (hNC : NeumannCoveringLemma) (n : ℕ) : iFun n ≤ hFun n := by
  apply sSup_le
  rintro a ⟨G, inst, hom, rfl⟩
  exact le_trans (iotaG_le_aG hNC G) (le_sSup ⟨G, inst, hom, rfl⟩)

/-- An elementary identity used to compare the two forms of the error term. -/
theorem sqrt_div_identity {x : ℝ} (hx : 0 < x) (c u : ℝ) :
    (c * (u / Real.sqrt x) + 1 / x) * x = 1 + c * Real.sqrt x * u := by
  have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx)
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  field_simp
  linear_combination (-(c * u)) * hsq

open Filter Topology in
/-- **Corollary 10.1** (Least index of an abelian subgroup): `log₂ i(n) = n/2 + o(n)`. -/
theorem log2i_asymptotics (hNeu : NeumannCentreQuotientFinite) (hSchur : SchurDerivedFinite)
    (hHall : HallStemTheorem) (hPyber : PyberCentreIndex) (hNVL : NeumannVaughanLeeBound)
    (hE : ExtraspecialExists) (hNC : NeumannCoveringLemma) :
    Filter.Tendsto (fun n : ℕ => (log2i n - (n : ℝ) / 2) / n) Filter.atTop (nhds 0) := by
  obtain ⟨C, hC, hup⟩ := log2h_upper hNeu hSchur hHall hPyber hNVL
  have hb : Tendsto (fun n : ℕ => C * ((Real.log ((n : ℝ) + 2)) ^ 3 / Real.sqrt n) + 1 / (n : ℝ))
      atTop (𝓝 0) := by
    have h1 := log_cube_div_sqrt_tendsto.const_mul C
    have h2 : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    simpa using h1.add h2
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hs : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn0.le
  obtain ⟨hhne, hhup⟩ := hup n hn
  have hifin : iFun n ≠ ⊤ := by
    intro htop
    exact hhne (top_le_iff.mp (htop ▸ iFun_le_hFun hNC n))
  have htoNat : (iFun n).toNat ≤ (hFun n).toNat := ENat.toNat_le_toNat (iFun_le_hFun hNC n) hhne
  -- upper bound for `log₂ i(n)`
  have hmono : log2i n ≤ log2h n := by
    rcases Nat.eq_zero_or_pos ((iFun n).toNat) with h0 | h0
    · have h1 : log2i n = 0 := by unfold log2i; rw [h0]; simp
      rw [h1]
      exact log2h_nonneg n
    · unfold log2i log2h
      exact Real.logb_le_logb_of_le (by norm_num)
        (by exact_mod_cast h0 : (0:ℝ) < (((iFun n).toNat : ℕ) : ℝ))
        (by exact_mod_cast htoNat)
  have hupper : log2i n ≤ (n : ℝ) / 2 + C * Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3 :=
    le_trans hmono hhup
  -- lower bound for `log₂ i(n)`
  have hlower : (n : ℝ) / 2 - 1 ≤ log2i n := by
    set k : ℕ := (n - 1) / 2 with hkdef
    have hkn : 2 * k + 1 ≤ n := by omega
    have hge := iFun_ge_extraspecial hE k n hkn
    have hkle : 2 ^ k ≤ (iFun n).toNat := by
      have := ENat.toNat_le_toNat hge hifin
      rwa [ENat.toNat_natCast] at this
    have hkR : ((2 : ℝ) ^ k) ≤ ((iFun n).toNat : ℝ) := by
      have h' : ((2 ^ k : ℕ) : ℝ) ≤ (((iFun n).toNat : ℕ) : ℝ) := by exact_mod_cast hkle
      simpa using h'
    have hlogk : (k : ℝ) ≤ log2i n := by
      unfold log2i
      have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (x := (2 : ℝ) ^ k)
        (by positivity) hkR
      simpa [Real.logb_pow, Real.logb_self_eq_one] using this
    have hkR2 : ((n : ℝ) - 2) / 2 ≤ (k : ℝ) := by
      have hnk : n ≤ 2 * k + 2 := by omega
      have h2 : (n : ℝ) ≤ 2 * (k : ℝ) + 2 := by exact_mod_cast hnk
      linarith
    linarith
  -- assemble
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hn0, div_le_iff₀ hn0]
  have habs : |log2i n - (n : ℝ) / 2| ≤ 1 + C * Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3 := by
    rw [abs_le]
    constructor
    · have hpos : 0 ≤ C * Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3 := by
        have : (0 : ℝ) ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith)
        positivity
      linarith
    · linarith
  exact le_trans habs (le_of_eq (sqrt_div_identity hn0 C _).symm)

/-- A rearrangement identity: `c * (u / √x) * x = c * (√x * u)` for `0 < x`. -/
theorem sqrt_cube_mul {x : ℝ} (hx : 0 < x) (c u : ℝ) :
    c * (u / Real.sqrt x) * x = c * (Real.sqrt x * u) := by
  have h := sqrt_div_identity hx c u
  have hx' : (1 : ℝ) / x * x = 1 := by field_simp
  have h1 : (c * (u / Real.sqrt x) + 1 / x) * x = c * (u / Real.sqrt x) * x + 1 / x * x := by ring
  rw [h1, hx'] at h
  linarith

open Filter Topology in
/-- **Corollary 10.2** (Asymptotic extremality is concentrated in 2-groups).

Pyber's centre-index theorem and the Neumann–Vaughan-Lee bound enter through Theorems 7.1
and 8.2 and are therefore stated as explicit hypotheses. -/
theorem extremality_concentrated_in_two_groups (hPyber : PyberCentreIndex)
    (hNVL : NeumannVaughanLeeBound)
    (Gr : ℕ → Type) [∀ r, Group (Gr r)] [∀ r, Finite (Gr r)] (nr : ℕ → ℕ)
    (hn : ∀ r, omegaG (Gr r) = ((nr r : ℕ) : ℕ∞))
    (hnr : Filter.Tendsto nr Filter.atTop Filter.atTop)
    (hextr : Filter.Tendsto (fun r => ((nr r : ℝ) / 2 - log2a (Gr r)) / (nr r : ℝ))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
        (fun r => ((nr r : ℝ) - ((omegaG (centralizerDerived (Gr r) : Type _)).toNat : ℝ))
          / (nr r : ℝ))
        Filter.atTop (nhds 0) ∧
      ∀ᶠ r in Filter.atTop,
        (∃ Q : Sylow 2 (centralizerDerived (Gr r) : Type _), ¬ ∀ x y : Q, Commute x y) ∧
        (∀ (s : ℕ), s.Prime → s ≠ 2 → ∀ Q : Sylow s (centralizerDerived (Gr r) : Type _),
          ∀ x y : Q, Commute x y) := by
  classical
  obtain ⟨C₂, hC₂, hfr⟩ := centralizer_derived_reduction hPyber hNVL
  obtain ⟨C₃, hC₃, hnil⟩ := nilpotent_sqrt_bound hNVL
  set K : ℝ := 4 * C₂ + C₃ with hKdef
  have hK0 : 0 < K := by rw [hKdef]; linarith
  set e : ℕ → ℝ := fun r => ((nr r : ℝ) / 2 - log2a (Gr r)) / (nr r : ℝ) with hedef
  set v : ℕ → ℝ := fun r => K * ((Real.log ((nr r : ℝ) + 2)) ^ 3 / Real.sqrt (nr r)) with hvdef
  have hvlim : Tendsto v atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => K * ((Real.log ((k : ℝ) + 2)) ^ 3 / Real.sqrt k))
        atTop (𝓝 0) := by simpa using log_cube_div_sqrt_tendsto.const_mul K
    exact h1.comp hnr
  have hn2 : ∀ᶠ r in atTop, 2 ≤ nr r := hnr.eventually_ge_atTop 2
  -- the pointwise estimates
  have main : ∀ r, 2 ≤ nr r →
      (((nr r : ℝ) - ((omegaG (centralizerDerived (Gr r) : Type _)).toNat : ℝ)) / (nr r : ℝ)
          ≤ 2 * e r + 2 * v r)
        ∧ 0 ≤ ((nr r : ℝ) - ((omegaG (centralizerDerived (Gr r) : Type _)).toNat : ℝ))
            / (nr r : ℝ)
        ∧ ((∀ (s : ℕ) (Q : Sylow s (centralizerDerived (Gr r) : Type _)), s = 2 →
              ∀ x y : Q, Commute x y) → (0.03 : ℝ) ≤ e r + v r)
        ∧ ((∃ (q₁ q₂ : ℕ) (_ : q₁.Prime) (_ : q₂.Prime)
              (Q₁ : Sylow q₁ (centralizerDerived (Gr r) : Type _))
              (Q₂ : Sylow q₂ (centralizerDerived (Gr r) : Type _)),
              q₁ ≠ q₂ ∧ (¬ ∀ x y : Q₁, Commute x y) ∧ (¬ ∀ x y : Q₂, Commute x y)) →
            (1 / 6 : ℝ) ≤ e r + v r) := by
    intro r hr2
    have hn1 : 1 ≤ nr r := by omega
    have hnR : (2 : ℝ) ≤ (nr r : ℝ) := by exact_mod_cast hr2
    have hn0 : (0 : ℝ) < (nr r : ℝ) := by linarith
    have hsn : (0 : ℝ) < Real.sqrt (nr r) := Real.sqrt_pos.mpr hn0
    set W : ℝ := Real.sqrt (nr r) * (Real.log ((nr r : ℝ) + 2)) ^ 3 with hWdef
    have hW0 : 0 ≤ W := by
      rw [hWdef]
      have : (0 : ℝ) ≤ Real.log ((nr r : ℝ) + 2) := Real.log_nonneg (by linarith)
      positivity
    have hvW : v r * (nr r : ℝ) = K * W := by
      rw [hvdef, hWdef]
      exact sqrt_cube_mul hn0 K _
    have heW : e r * (nr r : ℝ) = (nr r : ℝ) / 2 - log2a (Gr r) := by
      rw [hedef]
      field_simp
    -- the centralizer of the derived subgroup
    have : Group.IsNilpotent (centralizerDerived (Gr r) : Type _) :=
      centralizerDerived_isNilpotent (Gr r)
    set m : ℕ := (omegaG (centralizerDerived (Gr r) : Type _)).toNat with hmdef
    have hmeq : omegaG (centralizerDerived (Gr r) : Type _) = (m : ℕ∞) :=
      (ENat.natCast_toNat omegaG_ne_top).symm
    have hmn : m ≤ nr r := by
      have h1 : (m : ℕ∞) ≤ ((nr r : ℕ) : ℕ∞) := by
        rw [← hmeq, ← hn r]; exact omegaG_subgroup_le _
      exact_mod_cast h1
    have hmR : (m : ℝ) ≤ (nr r : ℝ) := by exact_mod_cast hmn
    have hstep1 := hfr (Gr r) (nr r) hr2 (hn r)
    have hlogn : C₂ * (Real.log ((nr r : ℝ) + 2)) ^ 4 ≤ C₂ * (4 * W) := by
      refine mul_le_mul_of_nonneg_left ?_ hC₂.le
      rw [hWdef]
      exact log_pow_four_le_sqrt_log_cube hn1 le_rfl
    have hmono : C₃ * Real.sqrt m * (Real.log ((m : ℝ) + 2)) ^ 3 ≤ C₃ * W := by
      rw [hWdef, ← mul_assoc]
      exact sqrt_log_cube_mono hC₃.le hmn
    obtain ⟨hnilA, hnilB, hnilD⟩ := hnil (centralizerDerived (Gr r) : Type _) m
      (centralizerDerived_isNilpotent (Gr r)) hmeq
    -- transfer to `Gr r`
    have htrans : ∀ X : ℝ, log2a (centralizerDerived (Gr r) : Type _)
        ≤ X + C₃ * Real.sqrt m * (Real.log ((m : ℝ) + 2)) ^ 3 → log2a (Gr r) ≤ X + K * W := by
      intro X hX
      have h := le_trans hstep1 (by linarith : log2a (centralizerDerived (Gr r) : Type _)
        + C₂ * (Real.log ((nr r : ℝ) + 2)) ^ 4 ≤ X + C₃ * W + C₂ * (4 * W))
      rw [hKdef]
      linarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h1 := htrans ((m : ℝ) / 2) hnilA
      rw [div_le_iff₀ hn0]
      have h2 : (2 * e r + 2 * v r) * (nr r : ℝ)
          = 2 * (e r * (nr r : ℝ)) + 2 * (v r * (nr r : ℝ)) := by ring
      rw [h2, hvW, heW]
      linarith
    · refine div_nonneg (by linarith) hn0.le
    · intro h2ab
      have h1 := htrans (0.47 * (m : ℝ)) (hnilD h2ab)
      have h2 : (0.47 : ℝ) * (m : ℝ) ≤ 0.47 * (nr r : ℝ) :=
        mul_le_mul_of_nonneg_left hmR (by norm_num)
      have h3 : (0.03 : ℝ) * (nr r : ℝ) ≤ (e r + v r) * (nr r : ℝ) := by
        have h4 : (e r + v r) * (nr r : ℝ) = e r * (nr r : ℝ) + v r * (nr r : ℝ) := by ring
        rw [h4, hvW, heW]
        linarith
      exact le_of_mul_le_mul_right (by linarith [h3]) hn0
    · intro htwo
      have h1 := htrans ((m : ℝ) / 3) (hnilB htwo)
      have h3 : (1 / 6 : ℝ) * (nr r : ℝ) ≤ (e r + v r) * (nr r : ℝ) := by
        have h4 : (e r + v r) * (nr r : ℝ) = e r * (nr r : ℝ) + v r * (nr r : ℝ) := by ring
        rw [h4, hvW, heW]
        linarith
      exact le_of_mul_le_mul_right (by linarith [h3]) hn0
  constructor
  · have hg : Tendsto (fun r => 2 * e r + 2 * v r) atTop (𝓝 (0 : ℝ)) := by
      simpa using (hextr.const_mul (2 : ℝ)).add (hvlim.const_mul (2 : ℝ))
    refine squeeze_zero' (g := fun r => 2 * e r + 2 * v r) ?_ ?_ hg
    · filter_upwards [hn2] with r hr using (main r hr).2.1
    · filter_upwards [hn2] with r hr using (main r hr).1
  · have hsmall : ∀ᶠ r in atTop, e r + v r < 0.03 := by
      have h : Tendsto (fun r => e r + v r) atTop (𝓝 (0 : ℝ)) := by
        simpa using hextr.add hvlim
      exact h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 0.03))
    filter_upwards [hn2, hsmall] with r hr2 hsm
    obtain ⟨-, -, h03, h16⟩ := main r hr2
    have hex : ∃ Q : Sylow 2 (centralizerDerived (Gr r) : Type _), ¬ ∀ x y : Q, Commute x y := by
      by_contra hcon
      push Not at hcon
      have h2ab : ∀ (s : ℕ) (Q : Sylow s (centralizerDerived (Gr r) : Type _)), s = 2 →
          ∀ x y : Q, Commute x y := by
        intro s Q hs
        subst hs
        exact hcon Q
      linarith [h03 h2ab]
    refine ⟨hex, ?_⟩
    intro s hs hs2 Q x y
    by_contra hc
    obtain ⟨Q₂, hQ₂⟩ := hex
    have := h16 ⟨s, 2, hs, Nat.prime_two, Q, Q₂, hs2, fun hall => hc (hall x y), hQ₂⟩
    linarith

end AbelianCovers

#print axioms AbelianCovers.main_theorem
#print axioms AbelianCovers.hFun_root_tendsto
