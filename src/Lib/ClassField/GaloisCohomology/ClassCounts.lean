module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import Lib.ClassField.GaloisCohomology.ContinuousCocycles
public import Lib.General.Algebra.FittingIdealsAndLengths

/-!
# Counting cocycles through their cohomology classes

Counts of continuous 1-cocycles are best stated for cohomology classes, which keep their meaning for
infinite coefficient modules. This file relates the two. Let `π` be a map from the continuous
1-cocycles `New.Z1 ρ` with kernel the coboundaries `New.B1 ρ`, such as the class map to `H¹`.

* `New.card_eq_card_map_mul_card_inf_B1`, `New.length_eq_length_map_add_length_inf_B1`: a group `W`
  of cocycles has `|W| = |π(W)| · |W ∩ B¹|`, and the same for lengths.
* `New.card_B1_mul_card_invariants`: `|B¹| · |H⁰| = |M|` for a finite module `M`.
* `New.card_inf_vanishingAt_eq_card_map`,
  `New.length_inf_vanishingAt_eq_length_map`, `New.infVanishingAtEquivMap`: let `γ` act by a
  scalar `ζ` with `ζ - 1` a unit. Then cocycles that vanish at `γ` (`New.vanishingAt`) meet `B¹`
  trivially. In a group `W ⊇ B¹` of cocycles, those that vanish at `γ` are isomorphic to the
  classes of `W`, so have as many elements and the same length.
* `New.DiscreteModule.toTopRep`, `New.DiscreteModule.classMap`: a discrete module as Mathlib's
  topological representation over `ℤ`, and the map from its continuous 1-cocycles onto its
  continuous cohomology `continuousCohomology 1`, with kernel `B¹` (`ker_classMap`), from Tau
  Ceti's comparison of the explicit `H¹` with Mathlib's.
* `New.DiscreteModule.quotB1EquivH1`: the explicit `H¹ = Z¹ / B¹` is `continuousCohomology 1`.

## Relation to the literature

Known; see J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. I, §2.
-/

@[expose] public section

noncomputable section

namespace New

open Module

variable {R G M : Type*} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M]
  [Module R M] [TopologicalSpace M] [DiscreteTopology M] {ρ : Representation R G M}

/-! ### Counting through classes -/

/-- Let `π` be an additive map on the continuous 1-cocycles with kernel the coboundaries `B¹`. A
group `W` of cocycles has as many elements as its image under `π` times its intersection with
`B¹`. -/
theorem card_eq_card_map_mul_card_inf_B1 {H : Type*} [AddGroup H] (π : Z1 ρ →+ H)
    (hπ : π.ker = (B1 ρ).toAddSubgroup) (W : AddSubgroup (Z1 ρ)) :
    Nat.card W = Nat.card (W.map π) * Nat.card ↥(W ⊓ (B1 ρ).toAddSubgroup) := by
  rw [← hπ, ← AddSubgroup.relIndex_ker, mul_comm, AddSubgroup.relIndex,
    ← AddSubgroup.card_mul_index (π.ker.addSubgroupOf W), inf_comm,
    ← AddSubgroup.addSubgroupOf_map_subtype,
    AddSubgroup.card_map_of_injective W.subtype_injective]

/-- Let `π` be an `R`-linear map on the continuous 1-cocycles with kernel the coboundaries `B¹`. A
submodule `W` of cocycles has the length of its image under `π` plus that of its intersection with
`B¹`. -/
theorem length_eq_length_map_add_length_inf_B1 {H : Type*} [AddCommGroup H] [Module R H]
    (π : Z1 ρ →ₗ[R] H) (hπ : LinearMap.ker π = B1 ρ) (W : Submodule R (Z1 ρ)) :
    length R W = length R (W.map π) + length R ↥(W ⊓ B1 ρ) := by
  rw [← relLength_add_length_inf W (B1 ρ), ← hπ, relLength_ker]

/-- The coboundary `g ↦ ρ g m - m` of `m`, as a continuous 1-cocycle, when the orbit maps of `ρ` are
continuous. -/
def coboundaryZ1 (hρ : ∀ m : M, Continuous fun g : G ↦ ρ g m) : M →ₗ[R] Z1 ρ :=
  (coboundaryMap ρ).codRestrict (Z1 ρ) fun m ↦
    ⟨(hρ m).sub continuous_const, fun g h ↦ by simp [map_sub]⟩

lemma coe_coboundaryZ1_apply (hρ : ∀ m : M, Continuous fun g : G ↦ ρ g m) (m : M) (g : G) :
    (coboundaryZ1 hρ m : G → M) g = ρ g m - m :=
  rfl

/-- When the orbit maps of `ρ` are continuous, the coboundaries `B¹` are the image of `M`. -/
lemma range_coboundaryZ1 (hρ : ∀ m : M, Continuous fun g : G ↦ ρ g m) :
    LinearMap.range (coboundaryZ1 hρ) = B1 ρ := by
  ext z
  rw [mem_B1_iff, LinearMap.mem_range]
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨m, fun _ ↦ rfl⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, Subtype.ext (funext hm)⟩

/-- For a finite module `M` on which `G` acts with continuous orbit maps, the coboundaries number
`|M| / |H⁰|`: `|B¹| · |M^G| = |M|`. -/
theorem card_B1_mul_card_invariants (hρ : ∀ m : M, Continuous fun g : G ↦ ρ g m) :
    Nat.card (B1 ρ) * Nat.card ρ.invariants = Nat.card M := by
  have h_ker : LinearMap.ker (coboundaryZ1 hρ) = ρ.invariants := by
    ext m
    rw [LinearMap.mem_ker, Representation.mem_invariants, Subtype.ext_iff, funext_iff]
    exact forall_congr' fun g ↦ sub_eq_zero
  rw [← range_coboundaryZ1 hρ, ← h_ker,
    Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (coboundaryZ1 hρ)),
    Nat.card_congr (coboundaryZ1 hρ).quotKerEquivRange.toEquiv, mul_comm]

/-! ### Normalised cocycles -/

variable (ρ) in
/-- The continuous 1-cocycles of `ρ` that vanish at `γ`. -/
def vanishingAt (γ : G) : Submodule R (Z1 ρ) :=
  LinearMap.ker ((LinearMap.proj γ).comp (Z1 ρ).subtype)

@[simp]
lemma mem_vanishingAt {γ : G} {z : Z1 ρ} : z ∈ vanishingAt ρ γ ↔ (z : G → M) γ = 0 :=
  Iff.rfl

section Normalised

variable {γ : G} {ζ : R} (hγ : ∀ m : M, ρ γ m = ζ • m) (hζ : IsUnit (ζ - 1))
include hγ hζ


/-- If `γ` acts by a scalar `ζ` with `ζ - 1` a unit, a coboundary that vanishes at `γ` is zero. -/
theorem eq_zero_of_mem_B1_of_apply_eq_zero {z : Z1 ρ} (hz : z ∈ B1 ρ) (hzγ : (z : G → M) γ = 0) :
    z = 0 := by
  obtain ⟨m, hm⟩ := mem_B1_iff.1 hz
  have hm0 : m = 0 := hζ.smul_left_cancel.1 <| by
    rw [smul_zero, sub_smul, one_smul, ← hγ, hm, hzγ]
  ext g
  simp [← hm, hm0]

/-- If `γ` acts by a scalar `ζ` with `ζ - 1` a unit, every cocycle differs by a coboundary from one
that vanishes at `γ`. -/
theorem exists_sub_mem_B1_apply_eq_zero (hρ : ∀ m : M, Continuous fun g : G ↦ ρ g m)
    (z : Z1 ρ) : ∃ b ∈ B1 ρ, z - b ∈ vanishingAt ρ γ := by
  set m : M := hζ.unit⁻¹ • (z : G → M) γ
  have hm : (ζ - 1) • m = (z : G → M) γ := by
    rw [← hζ.unit_spec, ← Units.smul_def, smul_inv_smul]
  refine ⟨coboundaryZ1 hρ m, range_coboundaryZ1 hρ ▸ LinearMap.mem_range_self _ _, ?_⟩
  rw [mem_vanishingAt, Submodule.coe_sub, Pi.sub_apply, coe_coboundaryZ1_apply, hγ, ← hm,
    sub_smul, one_smul, sub_self]

variable (hρ : ∀ m : M, Continuous fun g : G ↦ ρ g m)
include hρ

/-- Let `γ` act by a scalar `ζ` with `ζ - 1` a unit, and let `π` be an additive map on the cocycles
with kernel `B¹`. For a group `W` of cocycles containing `B¹`, the members of `W` that vanish at
`γ` map onto the image of `W`: each class has a representative that vanishes at `γ`. -/
theorem map_inf_vanishingAt_eq_map {H : Type*} [AddGroup H] (π : Z1 ρ →+ H)
    (hπ : π.ker = (B1 ρ).toAddSubgroup) {W : AddSubgroup (Z1 ρ)}
    (hBW : (B1 ρ).toAddSubgroup ≤ W) :
    (W ⊓ (vanishingAt ρ γ).toAddSubgroup).map π = W.map π := by
  refine le_antisymm (AddSubgroup.map_mono inf_le_left) ?_
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨b, hb, hzb⟩ := exists_sub_mem_B1_apply_eq_zero hγ hζ hρ z
  have hπb : π b = 0 := AddMonoidHom.mem_ker.1 (hπ ▸ hb)
  exact ⟨z - b, AddSubgroup.mem_inf.2 ⟨W.sub_mem hz (hBW hb), hzb⟩, by
    rw [map_sub, hπb, sub_zero]⟩

/-- Let `γ` act by a scalar `ζ` with `ζ - 1` a unit, and let `π` be an `R`-linear map on the
cocycles with kernel `B¹`. For a submodule `W` of cocycles containing `B¹`, the members of `W` that
vanish at `γ` map onto the image of `W`. -/
theorem map_inf_vanishingAt_eq_map_of_linear {H : Type*} [AddCommGroup H] [Module R H]
    (π : Z1 ρ →ₗ[R] H) (hπ : LinearMap.ker π = B1 ρ) {W : Submodule R (Z1 ρ)} (hBW : B1 ρ ≤ W) :
    (W ⊓ vanishingAt ρ γ).map π = W.map π := by
  apply Submodule.toAddSubgroup_injective
  exact map_inf_vanishingAt_eq_map hγ hζ hρ π.toAddMonoidHom
    (congrArg Submodule.toAddSubgroup hπ) ((Submodule.toAddSubgroup_le _ _).2 hBW)

variable {H : Type*} [AddGroup H] (π : Z1 ρ →+ H) (hπ : π.ker = (B1 ρ).toAddSubgroup)
include hπ

/-- Let `γ` act by a scalar `ζ` with `ζ - 1` a unit, and let `π` be an additive map on the cocycles
with kernel `B¹`. For a group `W` of cocycles containing `B¹`, `π` is an isomorphism from the
members of `W` that vanish at `γ` onto the classes `π(W)`. -/
def infVanishingAtEquivMap {W : AddSubgroup (Z1 ρ)} (hBW : (B1 ρ).toAddSubgroup ≤ W) :
    ↥(W ⊓ (vanishingAt ρ γ).toAddSubgroup) ≃+ W.map π :=
  AddEquiv.ofBijective
    ((π.comp (W ⊓ (vanishingAt ρ γ).toAddSubgroup).subtype).codRestrict (W.map π) fun z ↦
      AddSubgroup.mem_map_of_mem π (AddSubgroup.mem_inf.1 z.2).1)
    ⟨fun z z' h ↦ by
      have h' : π ((z : Z1 ρ) - z') = 0 := by
        rw [map_sub, sub_eq_zero]
        exact congrArg Subtype.val h
      have hv : (z : Z1 ρ) - z' ∈ vanishingAt ρ γ :=
        sub_mem (AddSubgroup.mem_inf.1 z.2).2 (AddSubgroup.mem_inf.1 z'.2).2
      have hB : (z : Z1 ρ) - z' ∈ B1 ρ := by
        rw [← Submodule.mem_toAddSubgroup, ← hπ]
        exact h'
      exact Subtype.ext <| sub_eq_zero.1 <| eq_zero_of_mem_B1_of_apply_eq_zero hγ hζ hB hv,
    fun ⟨y, hy⟩ ↦ by
      rw [← map_inf_vanishingAt_eq_map hγ hζ hρ π hπ hBW] at hy
      obtain ⟨z, hz, rfl⟩ := AddSubgroup.mem_map.1 hy
      exact ⟨⟨z, hz⟩, rfl⟩⟩

/-- Let `γ` act by a scalar `ζ` with `ζ - 1` a unit, and let `π` be an additive map on the cocycles
with kernel `B¹`. For a group `W` of cocycles containing `B¹`, the members of `W` that vanish at
`γ` are as many as the classes `π(W)`. -/
theorem card_inf_vanishingAt_eq_card_map {W : AddSubgroup (Z1 ρ)}
    (hBW : (B1 ρ).toAddSubgroup ≤ W) :
    Nat.card ↥(W ⊓ (vanishingAt ρ γ).toAddSubgroup) = Nat.card (W.map π) :=
  Nat.card_congr (infVanishingAtEquivMap hγ hζ hρ π hπ hBW).toEquiv

end Normalised

/-- Let `γ` act by a scalar `ζ` with `ζ - 1` a unit, and let `π` be an `R`-linear map on the
cocycles with kernel `B¹`. For a submodule `W` of cocycles containing `B¹`, the members of `W` that
vanish at `γ` have the length of the classes `π(W)`. -/
theorem length_inf_vanishingAt_eq_length_map {γ : G} {ζ : R} (hγ : ∀ m : M, ρ γ m = ζ • m)
    (hζ : IsUnit (ζ - 1)) (hρ : ∀ m : M, Continuous fun g : G ↦ ρ g m) {H : Type*}
    [AddCommGroup H] [Module R H] (π : Z1 ρ →ₗ[R] H) (hπ : LinearMap.ker π = B1 ρ)
    {W : Submodule R (Z1 ρ)} (hBW : B1 ρ ≤ W) :
    length R ↥(W ⊓ vanishingAt ρ γ) = length R (W.map π) := by
  have h_bot : W ⊓ vanishingAt ρ γ ⊓ B1 ρ = ⊥ := (Submodule.eq_bot_iff _).2 fun z hz ↦
    eq_zero_of_mem_B1_of_apply_eq_zero hγ hζ (Submodule.mem_inf.1 hz).2
      (Submodule.mem_inf.1 (Submodule.mem_inf.1 hz).1).2
  rw [length_eq_length_map_add_length_inf_B1 π hπ, h_bot,
    map_inf_vanishingAt_eq_map_of_linear hγ hζ hρ π hπ hBW,
    length_eq_zero (M := ↥(⊥ : Submodule R (Z1 ρ))), add_zero]

/-! ### The class map to Mathlib's continuous cohomology -/

namespace DiscreteModule

open TauCeti.ContCohomology

variable {R Γ : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] (A : DiscreteModule R Γ)

/-- The action of `Γ` on a discrete module `A`, as a distributive action on its underlying group. -/
abbrev distribMulAction : DistribMulAction Γ A := DistribMulAction.compHom A.V A.ρ

attribute [local instance] distribMulAction

instance : ContinuousSMul Γ A := ⟨A.continuous⟩

/-- The orbit maps `g ↦ g m` of a discrete module are continuous. -/
lemma continuous_orbit (m : A) : Continuous fun g : Γ ↦ A.ρ g m :=
  A.continuous.comp (continuous_id.prodMk continuous_const)

/-- A discrete module `A`, forgetting the coefficients `R`, as a topological representation of `Γ`
over `ℤ` (Tau Ceti's `TauCeti.ofDiscreteModule`). -/
abbrev toTopRep : TopRep ℤ Γ := TauCeti.ofDiscreteModule ℤ Γ A

/-- The continuous 1-cocycles of `A` are Tau Ceti's continuous 1-cocycles of the action. -/
theorem Z1_toAddSubgroup : (Z1 A.ρ).toAddSubgroup = TauCeti.ContCohomology.Z1 Γ A := by
  ext f
  simp only [Submodule.mem_toAddSubgroup, TauCeti.ContCohomology.mem_Z1_iff,
    groupCohomology.IsCocycle₁]
  exact and_congr Iff.rfl (forall₂_congr fun g h ↦ by rw [add_comm (f g)]; rfl)

variable [IsTopologicalGroup Γ]

/-- The map sending a continuous 1-cocycle of `A` to its class in Mathlib's continuous cohomology
`continuousCohomology 1` of `A`, through Tau Ceti's explicit `H¹`. -/
def classMap : Z1 A.ρ →+ continuousCohomology 1 A.toTopRep :=
  (explicitH1AddEquivContinuousCohomology Γ A).toAddMonoidHom.comp <| (H1pi Γ A).comp
    { toFun z := ⟨z, A.Z1_toAddSubgroup ▸ z.2⟩
      map_zero' := rfl
      map_add' _ _ := rfl }

theorem classMap_surjective : Function.Surjective A.classMap := by
  refine (explicitH1AddEquivContinuousCohomology Γ A).surjective.comp <|
    (QuotientAddGroup.mk'_surjective _).comp fun z ↦ ⟨⟨z, ?_⟩, rfl⟩
  rw [← Submodule.mem_toAddSubgroup, A.Z1_toAddSubgroup]
  exact z.2

/-- A continuous 1-cocycle has class `0` in `continuousCohomology 1` exactly when it is a
coboundary. -/
theorem ker_classMap : A.classMap.ker = (B1 A.ρ).toAddSubgroup := by
  ext z
  rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, mem_B1_iff]
  simp only [classMap, H1pi, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom, EmbeddingLike.map_eq_zero_iff, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf,
    TauCeti.ContCohomology.mem_B1_iff, groupCohomology.IsCoboundary₁]
  rfl

/-- The explicit `H¹`, continuous 1-cocycles modulo coboundaries, is Mathlib's
`continuousCohomology 1`, as an additive equivalence. -/
def quotB1EquivH1 : (Z1 A.ρ ⧸ B1 A.ρ) ≃+ continuousCohomology 1 A.toTopRep :=
  QuotientAddGroup.liftEquiv (B1 A.ρ).toAddSubgroup A.classMap_surjective A.ker_classMap.symm


end DiscreteModule

end New
