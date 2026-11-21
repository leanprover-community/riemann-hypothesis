import Development.AutomorphicArithmetic.FiniteIndexCoboundary
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecJFacts
open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology NumberField IsDedekindDomain

private theorem bkAbove_avg {k G W : Type} [Field k] [CharZero k] [Group G] [AddCommGroup W] [Module k W]
    (a : G → W →ₗ[k] W) (hmul : ∀ g h w, a (g * h) w = a g (a h w)) (f : G → W)
    (hf : ∀ g h, f (g * h) = f g + a g (f h)) (H : Subgroup G) [H.FiniteIndex] (x : W)
    (hx : ∀ h ∈ H, f h = a h x - x) : ∃ y, ∀ g, f g = a g y - y :=
  _root_.UpperTheory.finiteIndexCoboundary a hmul f hf H x hx

theorem UpperTheory.V.Loc.bkAbove :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (j : Ω →+* Om l) {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (φ : H →* GQ l) (ψ : H →* G F Ω), IsOpenEmbedding φ → (∀ h y, φ h (j y) = j (ψ h y)) → ∀ {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V] (ρ : Representation C (G F Ω) V), ∀ c ∈ Z1 ρ, ((fun h => c (ψ h)) ∈ finiteCocycles φ (ρ.comp ψ) ↔ (fun x : ↥(UpperTheory.V.Af.decJ F j) => c x.1.1) ∈ finiteCocycles ((MonoidHom.snd _ _).comp (UpperTheory.V.Af.decJ F j).subtype) (ρ.comp ((MonoidHom.fst _ _).comp (UpperTheory.V.Af.decJ F j).subtype))) := by
  intro F Ω _ _ _ _ _ _ l _ j H _ _ _ φ ψ hφ hj C V _ _ _ _ _ _ _ _ _ ρ c hc
  let θ : H →* ↥(UpperTheory.V.Af.decJ F j) := (ψ.prod φ).codRestrict _ (fun h y => hj h y)
  let s : ↥(UpperTheory.V.Af.decJ F j) →* GQ l := (MonoidHom.snd _ _).comp (UpperTheory.V.Af.decJ F j).subtype
  let p : ↥(UpperTheory.V.Af.decJ F j) →* G F Ω := (MonoidHom.fst _ _).comp (UpperTheory.V.Af.decJ F j).subtype
  have hs : IsOpenEmbedding s := (UpperTheory.V.Loc.decJFacts (F := F) j).1
  have hθ : Continuous θ := hs.isEmbedding.continuous_iff.2 hφ.continuous
  have hp : Continuous p := continuous_fst.comp continuous_subtype_val
  have hψ : Continuous ψ := hp.comp hθ
  constructor
  · rintro ⟨-, x, hx⟩
    refine ⟨⟨hc.1.comp hp, fun g h => hc.2 _ _⟩, ?_⟩
    haveI : CompactSpace (GQ l) := inferInstanceAs (CompactSpace (Om l ≃ₐ[ℚ_[l]] Om l))
    haveI : Finite (GQ l ⧸ φ.range) := Subgroup.quotient_finite_of_isOpen _ hφ.isOpen_range
    haveI : φ.range.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    haveI : (φ.range.comap s).FiniteIndex := ⟨by
      rw [Subgroup.index_comap]
      exact Subgroup.FiniteIndex.index_ne_zero⟩
    refine bkAbove_avg (k := ℚ_[l]) (fun g => (actC s (ρ.comp p) g).restrictScalars ℚ_[l]) ?_
      (fun g => c (p g) ⊗ₜ[ℚ_[l]] (1 : Bcr l)) ?_ (φ.range.comap s) x ?_
    · intro g h w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [actC]
      | add u v hu hv => simp only [map_add, hu, hv]
    · intro g h
      simp [actC, hc.2 (p g) (p h), TensorProduct.add_tmul]
    · rintro g ⟨h, hh⟩
      obtain rfl : θ h = g := hs.injective hh
      exact hx h
  · rintro ⟨-, x, hx⟩
    exact ⟨⟨hc.1.comp hψ, fun g h => (congrArg c (map_mul ψ g h)).trans (hc.2 _ _)⟩, x, fun h => hx (θ h)⟩
