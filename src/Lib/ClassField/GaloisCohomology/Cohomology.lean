module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ContinuousCohomologyIso
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import TauCeti.RepresentationTheory.Homological.ContCohomology.Additive
public import Lib.ClassField.GaloisCohomology.ClassCounts

/-!
# The cohomology of a discrete module

The cohomology `Hⁿ(Γ, A)` of a discrete module `A : New.DiscreteModule R Γ` is Mathlib's continuous
cohomology `continuousCohomology n` of the underlying discrete abelian group with its `Γ`-action, so
the object does not depend on `R`. The `R`-module structure comes from functoriality: `r` acts by
the map induced by `m ↦ r • m`. The explicit formulae in low degrees are API, through Tau Ceti's
comparisons of explicit cocycles with Mathlib's continuous cohomology.

* `New.DiscreteModule.H`: the cohomology `Hⁿ(Γ, A)`, with its `R`-module structure.
* `New.DiscreteModule.zeroEquiv`: `H⁰(Γ, A)` is the module of invariants.
* `New.DiscreteModule.π₁`, `New.DiscreteModule.ker_π₁`: the `R`-linear map from the continuous
  1-cocycles onto `H¹(Γ, A)`, with kernel the coboundaries.
* `New.DiscreteModule.π₂`, `New.DiscreteModule.H2EquivH`: the `R`-linear map from the continuous
  2-cocycles onto `H²(Γ, A)`, for a locally compact `Γ`, and the identification of the explicit
  `New.DiscreteModule.H2` with `H²(Γ, A)`.
* `New.DiscreteModule.card_eq_card_map_π₁_mul_card_inf_B1`,
  `New.DiscreteModule.length_eq_length_map_π₁_add_length_inf_B1`: the counts of
  `Lib.ClassField.GaloisCohomology.ClassCounts` for the classes in `H¹(Γ, A)`.

The `R`-module structure and the `R`-linearity of the comparisons are proved here because Tau Ceti
does not provide them yet; they belong in Tau Ceti.

## Relation to the literature

Known; see J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. I, §2.
-/

@[expose] public section

noncomputable section

namespace New.DiscreteModule

open CategoryTheory TauCeti.ContCohomology Module

variable {R Γ : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] (A : DiscreteModule R Γ)

attribute [local instance] distribMulAction

/-! ### The object and its `R`-module structure -/

/-- Multiplication by `r` on a discrete module `A`, as an equivariant additive map. -/
def smulHom (r : R) : A →+[Γ] A where
  toFun m := r • m
  map_smul' g m := ((A.ρ g).map_smul r m).symm
  map_zero' := smul_zero r
  map_add' := smul_add r

variable [IsTopologicalGroup Γ]

/-- The continuous cohomology `Hⁿ(Γ, A)` of a discrete module `A`: Mathlib's
`continuousCohomology n` of `A` as a topological representation over `ℤ`. -/
def H (n : ℕ) : Type := continuousCohomology n A.toTopRep

instance (n : ℕ) : AddCommGroup (A.H n) :=
  inferInstanceAs (AddCommGroup (continuousCohomology n A.toTopRep))

/-- Multiplication by `r` on `A`, as an endomorphism of the topological representation. -/
abbrev smulMor (r : R) : A.toTopRep ⟶ A.toTopRep :=
  TauCeti.ofDiscreteModuleMap (A.smulHom r).toAddMonoidHom.toIntLinearMap
    fun g m ↦ map_smul (A.smulHom r) g m


-- This belongs in Tau Ceti: the action of `R` on cohomology through coefficient maps.
/-- The action of `R` on `Hⁿ(Γ, A)`: `r` acts by the map induced by `m ↦ r • m`. -/
def smulRingHom (n : ℕ) : R →+* AddMonoid.End (A.H n) where
  toFun r := (TauCeti.ContinuousCohomology.coeffMap (A.smulMor r) n).hom.toLinearMap.toAddMonoidHom
  map_one' := by
    have h : A.smulMor 1 = 𝟙 _ :=
      TopRep.hom_ext (DFunLike.ext _ _ fun m ↦ one_smul R (m : A.V))
    ext x
    simp [h]
    rfl
  map_mul' r s := by
    have h : A.smulMor (r * s) = A.smulMor s ≫ A.smulMor r :=
      TopRep.hom_ext (DFunLike.ext _ _ fun m ↦ mul_smul r s (m : A.V))
    ext x
    simp [h, TauCeti.ContinuousCohomology.coeffMap_comp]
    rfl
  map_zero' := by
    have h : A.smulMor 0 = 0 :=
      TopRep.hom_ext (DFunLike.ext _ _ fun m ↦ zero_smul R (m : A.V))
    have h0 := TauCeti.ContinuousCohomology.map_zero (X := A.toTopRep) (Y := A.toTopRep)
      (ContinuousMonoidHom.id Γ) n
    ext x
    simp only [h, TauCeti.ContinuousCohomology.coeffMap_def]
    exact congrArg (fun f ↦ f.hom x) h0
  map_add' r s := by
    have h : A.smulMor (r + s) = A.smulMor r + A.smulMor s :=
      TopRep.hom_ext (DFunLike.ext _ _ fun m ↦ add_smul r s (m : A.V))
    have h2 := TauCeti.ContinuousCohomology.map_add (X := A.toTopRep) (Y := A.toTopRep)
      (ContinuousMonoidHom.id Γ) (A.smulMor r) (A.smulMor s) n
    ext x
    simp only [h, TauCeti.ContinuousCohomology.coeffMap_def]
    exact congrArg (fun f ↦ f.hom x) h2

-- This belongs in Tau Ceti: the `R`-module structure on the cohomology of a discrete `R`-module.
instance (n : ℕ) : Module R (A.H n) := Module.compHom (A.H n) (A.smulRingHom n)

lemma smul_def (n : ℕ) (r : R) (x : A.H n) :
    r • x = (TauCeti.ContinuousCohomology.coeffMap (A.smulMor r) n).hom x :=
  rfl

/-! ### Degree zero -/

-- This belongs in Tau Ceti: the `R`-linear form of `explicitH0IsoContinuousCohomology`.
/-- `H⁰(Γ, A)` is the module of invariants of `A`. -/
def zeroEquiv : A.H 0 ≃ₗ[R] A.ρ.invariants where
  toFun x := ⟨((explicitH0IsoContinuousCohomology Γ A).inv x : A), fun g ↦
    ((explicitH0IsoContinuousCohomology Γ A).inv x).2 g⟩
  invFun m := (explicitH0IsoContinuousCohomology Γ A).hom ⟨m, fun g ↦ m.2 g⟩
  left_inv x := (explicitH0IsoContinuousCohomology Γ A).inv_hom_id_apply x
  right_inv m := Subtype.ext <| congrArg Subtype.val
    ((explicitH0IsoContinuousCohomology Γ A).hom_inv_id_apply
      (⟨m, fun g ↦ m.2 g⟩ : TauCeti.ContCohomology.H0 Γ A))
  map_add' x y := Subtype.ext <| congrArg Subtype.val
    (map_add (ConcreteCategory.hom (explicitH0IsoContinuousCohomology Γ A).inv) x y)
  map_smul' r x := by
    obtain ⟨m, rfl⟩ : ∃ m, (explicitH0IsoContinuousCohomology Γ A).hom m = x :=
      ⟨(explicitH0IsoContinuousCohomology Γ A).inv x,
        (explicitH0IsoContinuousCohomology Γ A).inv_hom_id_apply x⟩
    apply Subtype.ext
    change (((explicitH0IsoContinuousCohomology Γ A).inv
        ((TauCeti.ContinuousCohomology.coeffMap (A.smulMor r) 0).hom
          ((explicitH0IsoContinuousCohomology Γ A).hom m)) : TauCeti.ContCohomology.H0 Γ A) : A) =
      r • (((explicitH0IsoContinuousCohomology Γ A).inv
        ((explicitH0IsoContinuousCohomology Γ A).hom m) : TauCeti.ContCohomology.H0 Γ A) : A)
    rw [explicitH0Iso_coeffMap, Iso.hom_inv_id_apply, Iso.hom_inv_id_apply, coe_explicitCoeff0]
    rfl

/-! ### Degree one -/

-- This belongs in Tau Ceti: the `R`-linear form of `explicitH1AddEquivContinuousCohomology`.
/-- The `R`-linear map sending a continuous 1-cocycle of `A` to its class in `H¹(Γ, A)`. -/
def π₁ : Z1 A.ρ →ₗ[R] A.H 1 where
  toFun := A.classMap
  map_add' := map_add A.classMap
  map_smul' r z := by
    change @Eq (continuousCohomology 1 A.toTopRep : Type) (A.classMap (r • z))
      ((TauCeti.ContinuousCohomology.coeffMap (A.smulMor r) 1).hom (A.classMap z))
    simp only [classMap, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom]
    rw [explicitH1AddEquivContinuousCohomology_coeffMap]
    refine congrArg _ ?_
    simp only [H1pi, QuotientAddGroup.mk'_apply, explicitCoeff1_mk]
    refine congrArg _ (Subtype.ext ?_)
    ext g
    symm
    refine (cocyclesMap1_apply Γ A.V Γ A.V (ContinuousMonoidHom.id Γ) _ _ _ _ g).trans ?_
    rfl

lemma π₁_apply (z : Z1 A.ρ) : A.π₁ z = A.classMap z := rfl

lemma π₁_surjective : Function.Surjective A.π₁ := A.classMap_surjective

/-- A continuous 1-cocycle has class `0` in `H¹(Γ, A)` exactly when it is a coboundary. -/
lemma ker_π₁ : LinearMap.ker A.π₁ = B1 A.ρ :=
  Submodule.toAddSubgroup_injective A.ker_classMap

/-- A group `W` of continuous 1-cocycles has as many elements as its classes in `H¹(Γ, A)` times
its intersection with the coboundaries. -/
theorem card_eq_card_map_π₁_mul_card_inf_B1 (W : Submodule R (Z1 A.ρ)) :
    Nat.card W = Nat.card (W.map A.π₁) * Nat.card ↥(W ⊓ B1 A.ρ) :=
  card_eq_card_map_mul_card_inf_B1 A.classMap A.ker_classMap W.toAddSubgroup

/-- A module `W` of continuous 1-cocycles has the length of its classes in `H¹(Γ, A)` plus that of
its intersection with the coboundaries. -/
theorem length_eq_length_map_π₁_add_length_inf_B1 (W : Submodule R (Z1 A.ρ)) :
    length R W = length R (W.map A.π₁) + length R ↥(W ⊓ B1 A.ρ) :=
  length_eq_length_map_add_length_inf_B1 A.π₁ A.ker_π₁ W

/-- The explicit `H¹`, continuous 1-cocycles modulo coboundaries, is `H¹(Γ, A)`, `R`-linearly. -/
def quotEquivH1 : (Z1 A.ρ ⧸ B1 A.ρ) ≃ₗ[R] A.H 1 :=
  (Submodule.quotEquivOfEq _ _ A.ker_π₁.symm).trans (A.π₁.quotKerEquivOfSurjective A.π₁_surjective)


/-! ### Restriction in degree one -/

section Restriction

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →ₜ* Γ)

/-- Restriction of continuous 1-cocycles along a continuous homomorphism `φ : G → Γ`:
`z ↦ z ∘ φ`. -/
def resZ1 : Z1 A.ρ →ₗ[R] Z1 (A.restrictAlong φ).ρ where
  toFun z := ⟨fun g ↦ (z : Γ → A) (φ g), z.2.1.comp φ.continuous, fun g h ↦
    (congrArg (z : Γ → A) (map_mul φ g h)).trans (z.2.2 (φ g) (φ h))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [IsTopologicalGroup Γ] [IsTopologicalGroup G] in
@[simp]
lemma coe_resZ1_apply (z : Z1 A.ρ) (g : G) : (A.resZ1 φ z : G → A) g = (z : Γ → A) (φ g) := rfl

omit [IsTopologicalGroup Γ] [IsTopologicalGroup G] in
lemma resZ1_mem_B1 {z : Z1 A.ρ} (hz : z ∈ B1 A.ρ) : A.resZ1 φ z ∈ B1 (A.restrictAlong φ).ρ := by
  obtain ⟨m, hm⟩ := mem_B1_iff.1 hz
  exact mem_B1_iff.2 ⟨m, fun g ↦ hm (φ g)⟩

-- This belongs in Tau Ceti: restriction on `H¹` with its value on classes of cocycles.
/-- Restriction `H¹(Γ, A) → H¹(G, A)` along a continuous homomorphism `φ : G → Γ`, on classes of
cocycles `z ↦ z ∘ φ`. -/
def resH1 : A.H 1 →ₗ[R] (A.restrictAlong φ).H 1 :=
  (A.restrictAlong φ).quotEquivH1.toLinearMap ∘ₗ
    (B1 A.ρ).mapQ (B1 (A.restrictAlong φ).ρ) (A.resZ1 φ) (fun _ hz ↦ A.resZ1_mem_B1 φ hz) ∘ₗ
      A.quotEquivH1.symm.toLinearMap

@[simp]
lemma resH1_π₁ (z : Z1 A.ρ) : A.resH1 φ (A.π₁ z) = (A.restrictAlong φ).π₁ (A.resZ1 φ z) := by
  have h : A.quotEquivH1.symm (A.π₁ z) = Submodule.Quotient.mk z :=
    (LinearEquiv.symm_apply_eq _).2 rfl
  simp only [resH1, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, h,
    Submodule.mapQ_apply]
  rfl

end Restriction

/-! ### Degree two -/

omit [IsTopologicalGroup Γ] in
/-- The continuous 2-cocycles of `A` are Tau Ceti's continuous 2-cocycles of the action. -/
theorem Z2_toAddSubgroup : (Z2 A.ρ).toAddSubgroup = TauCeti.ContCohomology.Z2 Γ A := by
  ext f
  simp only [Submodule.mem_toAddSubgroup, TauCeti.ContCohomology.mem_Z2_iff,
    groupCohomology.IsCocycle₂]
  refine and_congr Iff.rfl (forall₃_congr fun g h k ↦ ?_)
  change f (g * h, k) = f (g, h * k) - f (g, h) + A.ρ g (f (h, k)) ↔
    f (g * h, k) + f (g, h) = A.ρ g (f (h, k)) + f (g, h * k)
  constructor <;> intro h_eq
  · rw [h_eq]; abel
  · rw [eq_sub_of_add_eq h_eq]; abel

omit [IsTopologicalGroup Γ] in
/-- The 2-coboundaries of `A` are Tau Ceti's 2-coboundaries. -/
theorem B2_toAddSubgroup : (B2 A.ρ).toAddSubgroup = TauCeti.ContCohomology.B2 Γ A := by
  ext f
  simp only [Submodule.mem_toAddSubgroup, TauCeti.ContCohomology.mem_B2_iff]
  refine exists_congr fun c ↦ and_congr Iff.rfl ⟨fun h ↦ funext fun ⟨g, g'⟩ ↦ ?_, ?_⟩
  · rw [d1_apply, h g g']
    rfl
  · rintro rfl g g'
    rw [d1_apply]
    rfl

variable [LocallyCompactSpace Γ]

/-- The map sending a continuous 2-cocycle of `A` to its class in `H²(Γ, A)`, through Tau Ceti's
explicit `H²`. -/
def classMap₂ : Z2 A.ρ →+ continuousCohomology 2 A.toTopRep :=
  (explicitH2AddEquivContinuousCohomology Γ A).toAddMonoidHom.comp <|
    (QuotientAddGroup.mk' _).comp
      { toFun z := ⟨z, A.Z2_toAddSubgroup ▸ z.2⟩
        map_zero' := rfl
        map_add' _ _ := rfl }

-- This belongs in Tau Ceti: the `R`-linear form of `explicitH2AddEquivContinuousCohomology`.
/-- The `R`-linear map sending a continuous 2-cocycle of `A` to its class in `H²(Γ, A)`. -/
def π₂ : Z2 A.ρ →ₗ[R] A.H 2 where
  toFun := A.classMap₂
  map_add' := map_add A.classMap₂
  map_smul' r z := by
    change @Eq (continuousCohomology 2 A.toTopRep : Type) (A.classMap₂ (r • z))
      ((TauCeti.ContinuousCohomology.coeffMap (A.smulMor r) 2).hom (A.classMap₂ z))
    simp only [classMap₂, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom]
    rw [explicitH2AddEquivContinuousCohomology_coeffMap]
    refine congrArg _ ?_
    simp only [QuotientAddGroup.mk'_apply, explicitCoeff2_mk]
    refine congrArg _ (Subtype.ext ?_)
    ext ⟨g, h⟩
    symm
    refine (cocyclesMap2_apply Γ A.V Γ A.V (ContinuousMonoidHom.id Γ) _ _ _ _ g h).trans ?_
    rfl

lemma π₂_apply (z : Z2 A.ρ) : A.π₂ z = A.classMap₂ z := rfl

lemma π₂_surjective : Function.Surjective A.π₂ := by
  refine (explicitH2AddEquivContinuousCohomology Γ A).surjective.comp <|
    (QuotientAddGroup.mk'_surjective _).comp fun z ↦ ⟨⟨z, ?_⟩, rfl⟩
  rw [← Submodule.mem_toAddSubgroup, A.Z2_toAddSubgroup]
  exact z.2

/-- A continuous 2-cocycle has class `0` in `H²(Γ, A)` exactly when it is the coboundary of a
continuous 1-cochain. -/
lemma ker_π₂ : LinearMap.ker A.π₂ = (B2 A.ρ).comap (Z2 A.ρ).subtype := by
  ext z
  rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype,
    ← Submodule.mem_toAddSubgroup, A.B2_toAddSubgroup]
  change @Eq (continuousCohomology 2 A.toTopRep : Type) (A.classMap₂ z) 0 ↔ _
  simp only [classMap₂, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
    EmbeddingLike.map_eq_zero_iff, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff,
    AddSubgroup.mem_addSubgroupOf]
  rfl

/-- The explicit `H²(Γ, A)`, continuous 2-cocycles modulo coboundaries, is the cohomology
`H²(Γ, A)`. -/
def H2EquivH : A.H2 ≃ₗ[R] A.H 2 :=
  (Submodule.quotEquivOfEq _ _ A.ker_π₂.symm).trans
    (A.π₂.quotKerEquivOfSurjective A.π₂_surjective)


end New.DiscreteModule
