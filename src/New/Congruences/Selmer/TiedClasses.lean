module

public import Lib.ClassField.GaloisCohomology.ClassCounts
public import New.Congruences.Selmer.Count

/-!
# The tied Selmer group as a group of cohomology classes

The tied Selmer group `T.tiedSelmer R J x i a` is a module of cocycles with values in `T / a`, cut
out by the local conditions, the ties on `J` and vanishing at `γ_*`, which acts by a scalar `ζ_*`
with `ζ_* - 1` a unit. This file shows that it is a module of classes: it meets the coboundaries
`B¹` only in `0`, and it maps isomorphically onto the classes of the module
`T.tiedCocycles R J x i a` cut out by the same conditions without vanishing at `γ_*`, which
contains `B¹` when the ties are stable under coboundaries. So the count
`New.Selmer.SelmerDatum.exists_length_tiedSelmer_le` is a statement about cohomology classes.

* `New.Selmer.SelmerDatum.tiedCocycles`: the tied Selmer module without the normalisation at `γ_*`.
* `New.Selmer.SelmerDatum.tiedSelmer_inf_B1_eq_bot`: the tied Selmer group meets `B¹` in `0`.
* `New.Selmer.SelmerDatum.tiedSelmerEquivClasses`,
  `New.Selmer.SelmerDatum.card_tiedSelmer_eq_card_classes`: the tied Selmer group is isomorphic to
  the group of classes of `T.tiedCocycles` in Mathlib's `continuousCohomology 1`.
* `New.Selmer.SelmerDatum.length_tiedSelmer_eq_length_classes`,
  `New.Selmer.SelmerDatum.exists_length_tiedClasses_le`: the same for lengths, with the classes
  in the explicit `H¹ = Z¹ / B¹`, and the count `exists_length_tiedSelmer_le` restated for them.

Notions from other files:
* `New.Selmer.SelmerDatum.reductionModule`: the discrete Galois module `T / a`, for `a ∣ ℓ ^ M`.
* `New.Z1`, `New.B1`, `New.vanishingAt`: continuous 1-cocycles, coboundaries, and cocycles that
  vanish at a given element.
* `New.DiscreteModule.classMap`: the class map from `Z¹` onto `continuousCohomology 1`.

## Relation to the literature

Known: a cocycle that vanishes at an element acting by a scalar `ζ` with `ζ - 1` a unit is the
unique representative of its class with that property.
-/

@[expose] public section

noncomputable section

namespace New.Selmer.SelmerDatum

open Module Matrix.Module

variable {ℓ : ℕ} [ThePrime ℓ] {E : Type} [Field E] [EmbeddedNumberField E] [NumberField.IsCMField E]
  {S₀ : Finset (FinPlace E)} {g₀ : Gal(Ω/E)} {O n ι : Type} [CommRing O] [PadicIntegerRing O ℓ]
  [Fintype n] [DecidableEq n] (T : SelmerDatum ℓ S₀ g₀ O n) {M N : ℕ} {a : O}
  {V : ι → Gal(Ω/E) → Prop} {W : Set Gal(Ω/E)} {P₀ : FinPlace E} {R J : Finset (FinPlace E)}
  {q : ℕ} {x : FinPlace E → AuxPrimeData E q × (ι → O)} {i : ι}

/-- The tied Selmer module without the normalisation at `γ_*`: the locally constant cocycles with
values in `(O / a) ^ n` that are unramified outside `T.places ∪ R ∪ R̄`, obey the local conditions
`T.localRelations` and the ties of index `i` on `J`. -/
def tiedCocycles (R J : Finset (FinPlace E)) (x : FinPlace E → AuxPrimeData E q × (ι → O))
    (i : ι) (a : O) : Submodule O (Gal(Ω/E) → n → QuotSpan a) :=
  selmerModule T.ρ (unionWithConj T.places R) (T.localRelations ∪ tieRelations J x i) (QuotSpan a)

/-- A member of the tied Selmer group is a member of `T.tiedCocycles` that vanishes at `γ_*`. -/
lemma mem_tiedSelmer_iff {z : Gal(Ω/E) → n → QuotSpan a} :
    z ∈ T.tiedSelmer R J x i a ↔ z ∈ T.tiedCocycles R J x i a ∧ z T.γ = 0 := by
  simp only [tiedSelmer, tiedCocycles, mem_selmerModule_iff, mem_obeying, classRelations,
    Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h_cocycle, h_unr, h_obey, h_const⟩
    exact ⟨⟨h_cocycle, h_unr, fun f hf ↦ h_obey f (hf.imp_left .inl), h_const⟩,
      by simpa using h_obey _ (.inl (.inr rfl))⟩
  · rintro ⟨⟨h_cocycle, h_unr, h_obey, h_const⟩, hγ⟩
    refine ⟨h_cocycle, h_unr, ?_, h_const⟩
    rintro f ((hf | rfl) | hf)
    exacts [h_obey f (.inl hf), by simpa using hγ, h_obey f (.inr hf)]

/-- The discrete topology on `O / a`, the one used by `T.reductionModule`. -/
local instance (b : O) : TopologicalSpace (QuotSpan b) := ⊥

local instance (b : O) : DiscreteTopology (QuotSpan b) := ⟨rfl⟩

variable (ha : a ∣ ℓ ^ M)
include ha

/-- The members of `T.tiedCocycles` are continuous 1-cocycles of `T / a`. -/
lemma tiedCocycles_le_Z1 : T.tiedCocycles R J x i a ≤ Z1 (T.reductionModule ha).ρ := fun _ hz ↦
  have h := mem_selmerModule_iff.1 hz
  ⟨h.2.2.2.continuous, h.1⟩

/-- `T.tiedCocycles` as a module of continuous 1-cocycles of `T / a`. -/
abbrev tiedCocyclesZ1 (R J : Finset (FinPlace E)) (x : FinPlace E → AuxPrimeData E q × (ι → O))
    (i : ι) : Submodule O (Z1 (T.reductionModule ha).ρ) :=
  (T.tiedCocycles R J x i a).comap (Z1 (T.reductionModule ha).ρ).subtype

/-- The tied Selmer group as a module of continuous 1-cocycles of `T / a`: the members of
`T.tiedCocycles` that vanish at `γ_*`. -/
lemma comap_tiedSelmer_eq :
    (T.tiedSelmer R J x i a).comap (Z1 (T.reductionModule ha).ρ).subtype =
      T.tiedCocyclesZ1 ha R J x i ⊓ vanishingAt (T.reductionModule ha).ρ T.γ := by
  ext z
  exact T.mem_tiedSelmer_iff

lemma tiedSelmer_le_Z1 : T.tiedSelmer R J x i a ≤ Z1 (T.reductionModule ha).ρ := fun _ hz ↦
  T.tiedCocycles_le_Z1 ha (T.mem_tiedSelmer_iff.1 hz).1

/-- The element `γ_*` acts on `T / a` by the scalar `ζ_*`. -/
lemma reductionModule_ρ_γ (b : n → QuotSpan a) :
    (T.reductionModule ha).ρ T.γ b = T.ζ • b := by
  change T.ρ T.γ • b = T.ζ • b
  rw [T.ρ_γ, smul_assoc, one_smul]

/-- The tied Selmer group meets the coboundaries only in `0`: a coboundary `g ↦ g b - b` that
vanishes at `γ_*` has `(ζ_* - 1) b = 0`, so `b = 0`. -/
theorem tiedSelmer_inf_B1_eq_bot :
    (T.tiedSelmer R J x i a).comap (Z1 (T.reductionModule ha).ρ).subtype ⊓
      B1 (T.reductionModule ha).ρ = ⊥ :=
  (Submodule.eq_bot_iff _).2 fun _ hz ↦ eq_zero_of_mem_B1_of_apply_eq_zero
    (T.reductionModule_ρ_γ ha) T.isUnit_ζ_sub_one (Submodule.mem_inf.1 hz).2
    (T.apply_γ_eq_zero (Submodule.mem_inf.1 hz).1)

open scoped Classical in
/-- If `V i g` says that `g` acts trivially on `T / ℓ ^ M`, the module `T.tiedCocycles` for tied
primes `J` contains the coboundaries. -/
lemma B1_le_tiedCocyclesZ1 {x : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O)}
    (hp : IsTiedPrimes ℓ S₀ V W N P₀ J x)
    (hV : ∀ g : Gal(Ω/E), V i g ↔ reduceModPow ℓ M T.ρ g = 1) :
    B1 (T.reductionModule ha).ρ ≤ T.tiedCocyclesZ1 ha R J x i := fun z hz ↦ by
  obtain ⟨b, hb⟩ := mem_B1_iff.1 hz
  have h_eq : (z : Gal(Ω/E) → n → QuotSpan a) = fun g ↦ T.ρ g • b - b := (funext hb).symm
  change (z : Gal(Ω/E) → n → QuotSpan a) ∈ T.tiedCocycles R J x i a
  rw [h_eq]
  exact mem_selmerModule_of_subset (T.coboundary_mem_selmerModule hp hV ha b) .rfl
    fun v hv ↦ Finset.mem_union_left _ hv

variable {x : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O)}
  (hp : IsTiedPrimes ℓ S₀ V W N P₀ J x) (hV : ∀ g : Gal(Ω/E), V i g ↔ reduceModPow ℓ M T.ρ g = 1)
include hp hV

/-- The tied Selmer group has the length of the module of classes of `T.tiedCocycles` in the
explicit `H¹ = Z¹ / B¹` of `T / a`, which is `continuousCohomology 1` by
`New.DiscreteModule.quotB1EquivH1`. -/
theorem length_tiedSelmer_eq_length_classes :
    length O (T.tiedSelmer R J x i a) =
      length O ((T.tiedCocyclesZ1 ha R J x i).map (B1 (T.reductionModule ha).ρ).mkQ) := by
  rw [← (Submodule.comapSubtypeEquivOfLe (T.tiedSelmer_le_Z1 ha)).length_eq,
    T.comap_tiedSelmer_eq ha]
  exact length_inf_vanishingAt_eq_length_map (T.reductionModule_ρ_γ ha) T.isUnit_ζ_sub_one
    (T.reductionModule ha).continuous_orbit _ (Submodule.ker_mkQ _)
    (T.B1_le_tiedCocyclesZ1 ha hp hV)

/-- `New.Selmer.SelmerDatum.exists_length_tiedSelmer_le` for classes. Let `J` be a set of tied
primes, where `V i g` says that `g` acts trivially on `T / ℓ ^ M`, and let `M < N` and
`a ∣ ℓ ^ M`. The module of classes in `H¹ = Z¹ / B¹` of `T / a` of the cocycles unramified outside
`T.places ∪ J ∪ J̄` that obey the local conditions and the ties on `J` is no longer than the dual
`T.dualSelmer`, up to the local terms `T.placesTerm`. -/
theorem exists_length_tiedClasses_le (hN : M < N) :
    ∃ (A : ∀ v : FinPlace E, {A : ClosurePlace // IsPlaceOver A v}) (R : Finset (FinPlace E)),
      length O ((T.tiedCocyclesZ1 ha J J x i).map (B1 (T.reductionModule ha).ρ).mkQ) ≤
        length O (T.dualSelmer hp hV hN ha A R) + T.placesTerm := by
  rw [← T.length_tiedSelmer_eq_length_classes ha hp hV]
  exact T.exists_length_tiedSelmer_le hp hV hN ha

variable [IsTopologicalGroup Gal(Ω/E)]

/-- The tied Selmer group is isomorphic to the group of classes, in Mathlib's
`continuousCohomology 1` of `T / a`, of the module `T.tiedCocycles` without the normalisation at
`γ_*`. -/
def tiedSelmerEquivClasses :
    T.tiedSelmer R J x i a ≃+
      (T.tiedCocyclesZ1 ha R J x i).toAddSubgroup.map (T.reductionModule ha).classMap :=
  ((Submodule.comapSubtypeEquivOfLe (T.tiedSelmer_le_Z1 ha)).symm.toAddEquiv.trans
    (AddEquiv.addSubgroupCongr
      (congrArg Submodule.toAddSubgroup (T.comap_tiedSelmer_eq ha)))).trans <|
    infVanishingAtEquivMap (W := (T.tiedCocyclesZ1 ha R J x i).toAddSubgroup)
      (T.reductionModule_ρ_γ ha) T.isUnit_ζ_sub_one (T.reductionModule ha).continuous_orbit _
      (T.reductionModule ha).ker_classMap
      ((Submodule.toAddSubgroup_le _ _).2 (T.B1_le_tiedCocyclesZ1 ha hp hV))

/-- The tied Selmer group has as many elements as the group of classes of `T.tiedCocycles` in
`continuousCohomology 1` of `T / a`. -/
theorem card_tiedSelmer_eq_card_classes :
    Nat.card (T.tiedSelmer R J x i a) = Nat.card
      ((T.tiedCocyclesZ1 ha R J x i).toAddSubgroup.map (T.reductionModule ha).classMap) :=
  Nat.card_congr (T.tiedSelmerEquivClasses ha hp hV).toEquiv

end New.Selmer.SelmerDatum

end
