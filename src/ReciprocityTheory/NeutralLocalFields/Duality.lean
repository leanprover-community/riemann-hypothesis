module

public import Mathlib
public import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Representation

namespace Neutral.B1

section CohA

set_option linter.unusedVariables false

noncomputable section

open Representation

variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

section ContMaps

variable (R M)

variable {R M}

end ContMaps

def ContAction (rho : Representation R G M) : Prop :=
  Continuous (fun p : G × M => rho p.1 p.2)

variable (rho : Representation R G M)

def H0 : Submodule R M := rho.invariants

theorem mem_riemannRochSpace_iff_regularAt_everywhere (m : M) : m ∈ H0 rho ↔ ∀ g, rho g m = m := Iff.rfl

def Z1 : Submodule R (G → M) where
  carrier := {f | Continuous f ∧ ∀ g h, f (g * h) = f g + rho g (f h)}
  zero_mem' := ⟨continuous_const, fun g h => by simp⟩
  add_mem' := fun {f f'} hf hf' => ⟨hf.1.add hf'.1, fun g h => by
    simp only [Pi.add_apply, hf.2, hf'.2, map_add (f := _)]; abel⟩
  smul_mem' c f hf := ⟨hf.1.const_smul c, fun g h => by
    simp only [Pi.smul_apply, hf.2, map_smul, smul_add]⟩

def d0 : M →ₗ[R] (G → M) := LinearMap.pi fun g => rho g - LinearMap.id

def Bd1 : Submodule R (G → M) := LinearMap.range (d0 rho)

theorem mem_contCoboundaries1 (f : G → M) : f ∈ Bd1 rho ↔ ∃ m, ∀ g, f g = rho g m - m := by
  constructor
  · rintro ⟨m, rfl⟩; exact ⟨m, fun g => rfl⟩
  · rintro ⟨m, hm⟩; exact ⟨m, funext fun g => (hm g).symm⟩

abbrev H1 := Z1 rho ⧸ (Bd1 rho).comap (Z1 rho).subtype

section Restriction

variable {H : Type*} [Group H] [TopologicalSpace H] (phi : H →* G)

variable (hphi : Continuous phi)
include hphi

def restrictCocycles1 : Z1 rho →ₗ[R] Z1 (rho.comp phi) where
  toFun f := ⟨f.1 ∘ phi, f.2.1.comp hphi, fun g h => by
    simp only [Function.comp_apply, map_mul, MonoidHom.coe_comp]
    exact f.2.2 _ _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def resH1 : H1 rho →ₗ[R] H1 (rho.comp phi) :=
  Submodule.mapQ _ _ (restrictCocycles1 rho phi hphi) fun f hf => by
    obtain ⟨m, hm⟩ := (mem_contCoboundaries1 rho _).1 hf
    exact (mem_contCoboundaries1 _ _).2 ⟨m, fun h => hm (phi h)⟩

end Restriction

section Map

variable {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  (rho' : Representation R G M') (u : M →ₗ[R] M') (hu : Continuous u)
  (hequiv : ∀ g m, u (rho g m) = rho' g (u m))
include hu hequiv

end Map

section Pair

variable {G' : Type*} [Group G'] [TopologicalSpace G']
  {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  (rho' : Representation R G' M') (phi : G' →* G) (hphi : Continuous phi)
  (u : M →ₗ[R] M') (hu : Continuous u) (hcompat : ∀ g m, u (rho (phi g) m) = rho' g (u m))
include hphi hu hcompat

end Pair

section MapPair

variable {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  (rho' : Representation R G M') (u : M →ₗ[R] M') (hu : Continuous u)
  (hequiv : ∀ g m, u (rho g m) = rho' g (u m))

end MapPair

section RestrictionN

variable {H : Type*} [Group H] [TopologicalSpace H] (phi : H →* G)

variable (hphi : Continuous phi)
include hphi

end RestrictionN

section Tate

end Tate

end

end CohA

section Coh

noncomputable section

open Representation

variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

variable (rho : Representation R G M)

section Cup

variable {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  {P : Type*} [AddCommGroup P] [Module R P] [TopologicalSpace P]
  [IsTopologicalAddGroup P] [ContinuousConstSMul R P]
  (rho' : Representation R G M') (rhoP : Representation R G P)
  (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
  (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y))

section CupZ11

include hb hbe

end CupZ11

include hb hbe

end Cup

section Local

variable {I : Type*} {D : I → Type*} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
  (phi : ∀ i, D i →* G) (hphi : ∀ i, Continuous (phi i))

end Local

section Inertia

variable {D : Type*} [Group D] [TopologicalSpace D] (rhoD : Representation R D M)
  (J : Subgroup D)

def H1ur : Submodule R (H1 rhoD) :=
  LinearMap.ker (resH1 rhoD J.subtype continuous_subtype_val)

end Inertia

end

end Coh

section NatCoh

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [TopologicalSpace G]
  {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  (rho : Representation R G M) (rho' : Representation R G M') (u : M →ₗ[R] M') (hu : Continuous u)
  (hequiv : ∀ g m, u (rho g m) = rho' g (u m))

variable {I : Type*} {Dl : I → Type*} [∀ i, Group (Dl i)] [∀ i, TopologicalSpace (Dl i)]
  (phis : ∀ i, Dl i →* G) (hphis : ∀ i, Continuous (phis i))

end NatCoh

instance (priority := 100) continuousConstSMul_of_discrete {R M : Type*} [SMul R M]
    [TopologicalSpace M] [DiscreteTopology M] : ContinuousConstSMul R M :=
  ⟨fun _ => continuous_of_discreteTopology⟩

section Coeff

variable {R : Type*} [CommRing R] {Γ : Type*} [Group Γ]
  {M : Type*} [AddCommGroup M] [Module R M]

def charRep (χ : Γ →* Rˣ) : Representation R Γ R where
  toFun g := ((χ g : Rˣ) : R) • LinearMap.id
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_comm]

@[simp] theorem charRep_apply (χ : Γ →* Rˣ) (g : Γ) (x : R) :
    charRep χ g x = ((χ g : Rˣ) : R) * x := rfl

end Coeff

section Cup

variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [DiscreteTopology M]

variable {D : Type*} [Group D] [TopologicalSpace D]
  (χ : Γ →* Rˣ) (rho : Representation R Γ M) (φ : D →* Γ)

end Cup

section NatMaps

variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {Γ : Type*} [Group Γ] [TopologicalSpace Γ] (χ : Γ →* Rˣ)
  {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [DiscreteTopology M']
  (rho : Representation R Γ M) (rho' : Representation R Γ M') (u : M →ₗ[R] M')
  (hequiv : ∀ g m, u (rho g m) = rho' g (u m))

variable {I : Type*} {Dl : I → Type*} [∀ i, Group (Dl i)] [∀ i, TopologicalSpace (Dl i)]
  (phis : ∀ i, Dl i →* Γ) (hphis : ∀ i, Continuous (phis i))

end NatMaps

section Cyc

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosed L] [CharZero L]
  (n : ℕ) [NeZero n]

def cycN : (L ≃ₐ[K] L) →* (ZMod n)ˣ :=
  (modularCyclotomicCharacter L (HasEnoughRootsOfUnity.natCard_rootsOfUnity L n)).comp
    (MulSemiringAction.toRingAut (L ≃ₐ[K] L) L)

variable {K L n} in
theorem cycN_spec (σ : L ≃ₐ[K] L) (ζ : L) (h : ζ ^ n = 1) :
    σ ζ = ζ ^ ((cycN K L n σ : ZMod n)).val := by
  have hz : ζ ≠ 0 := by
    rintro rfl
    simp [NeZero.ne n] at h
  have ht : Units.mk0 ζ hz ∈ rootsOfUnity n L := by
    rw [mem_rootsOfUnity]; ext; simp [h]
  have := modularCyclotomicCharacter.spec L (HasEnoughRootsOfUnity.natCard_rootsOfUnity L n)
    (MulSemiringAction.toRingAut (L ≃ₐ[K] L) L σ) ht
  simpa [cycN] using this

end Cyc

section Local

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

abbrev GK : Type := PadicAlgCl p ≃ₐ[K] PadicAlgCl p

def inertiaSet : Set (GK p K) := {σ | ∀ x : PadicAlgCl p, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1}

def inertiaK : Subgroup (GK p K) := Subgroup.closure (inertiaSet p K)

abbrev cycK (n : ℕ) [NeZero n] : GK p K →* (ZMod n)ˣ := cycN K (PadicAlgCl p) n

variable {p K}

variable (p) in
def KbarMult : Type := Additive (PadicAlgCl p)ˣ

instance : AddCommGroup (KbarMult p) := inferInstanceAs (AddCommGroup (Additive (PadicAlgCl p)ˣ))
instance : TopologicalSpace (KbarMult p) := ⊥
instance : DiscreteTopology (KbarMult p) := ⟨rfl⟩

variable (p K) in
def kbarRep : Representation ℤ (GK p K) (KbarMult p) where
  toFun σ := AddMonoidHom.toIntLinearMap
    (MonoidHom.toAdditive (Units.map (σ : PadicAlgCl p →* PadicAlgCl p)))
  map_one' := by
    apply LinearMap.ext; intro x
    apply Units.ext
    rfl
  map_mul' σ τ := by
    apply LinearMap.ext; intro x
    apply Units.ext
    rfl

abbrev QZ : Type := ℚ ⧸ (Int.castAddHom ℚ).range

end Local

section Global

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

instance finite_DecInf (j : Ω →+* ℂ) : Finite (DecInf F j) := by
  classical
  refine Finite.of_injective (fun σ : DecInf F j => decide (∀ x, j (σ.1 x) = j x)) ?_
  intro σ τ h
  have hiff : (∀ x, j (σ.1 x) = j x) ↔ ∀ x, j (τ.1 x) = j x := by simpa using h
  have hσ := (mem_DecInf j σ.1).1 σ.2
  have hτ := (mem_DecInf j τ.1).1 τ.2
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  apply j.injective
  by_cases h1 : ∀ x, j (σ.1 x) = j x
  · rw [h1 x, hiff.1 h1 x]
  · have h2 : ¬ ∀ x, j (τ.1 x) = j x := fun h' => h1 (hiff.2 h')
    rw [hσ.resolve_left h1 x, hτ.resolve_left h2 x]

section unram

variable (S : Set (HeightOneSpectrum (𝓞 F)))

instance normal_NS : (NS Ω S).Normal := by
  unfold NS; exact Subgroup.is_normal_topologicalClosure _

end unram

variable [IsAlgClosure F Ω] {S : Finset (HeightOneSpectrum (𝓞 F))} {n : ℕ} [NeZero n]

instance finite_locGrp_inr (D : GData F Ω S n) (w : InfinitePlace F) :
    Finite (locGrp D (Sum.inr w)) :=
  inferInstanceAs (Finite (DecInf F (D.J w)))

end Global

section PTMaps

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {S : Finset (HeightOneSpectrum (𝓞 F))} {n : ℕ} [NeZero n] (D : GData F Ω S n)
  {M : Type} [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M] [DiscreteTopology M]
  (rho : Representation (ZMod n) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)

variable (inv : ∀ v : S, H2 ((charRep D.chi).comp (locF D v)) →ₗ[ZMod n] ZMod n)

end PTMaps

section PTMapsAll

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {S : Finset (HeightOneSpectrum (𝓞 F))} {n : ℕ} [NeZero n] (D : GData F Ω S n)
  {M : Type} [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M] [DiscreteTopology M]
  (rho : Representation (ZMod n) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)

variable (inv : ∀ i : S ⊕ InfinitePlace F, H2 ((charRep D.chi).comp (locHom D i)) →ₗ[ZMod n] ZMod n)

end PTMapsAll

section PTFam

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {S : Finset (HeightOneSpectrum (𝓞 F))} {n : ℕ} [NeZero n] (D : GData F Ω S n)

variable {M : Type} [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M] [DiscreteTopology M]
  (rho : Representation (ZMod n) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
  (hrho : ContAction rho)

end PTFam

section LubinTate

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K}

end LubinTate

section FGL

variable {R : Type} [CommRing R]

end FGL

section Division

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

end Division

section LTRecip

open ValuativeRel

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]

end LTRecip

section Hecke

variable (K : Type) [Field K] [NumberField K]

variable {K}

end Hecke

end Neutral.B1
