module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite IsLocalRing

namespace GlobalTheory.EtC.Psi
open GlobalTheory.EtC.Rel

section Ring

theorem isLocalRing_integralClosure (O Ω : Type) [CommRing O] [HenselianLocalRing O] [Field Ω] [Algebra O Ω] :
    IsLocalRing (integralClosure O Ω) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  let S := Algebra.adjoin O {(x : Ω)}
  haveI : Module.Finite O S := Module.Finite.iff_fg.2 (IsIntegral.fg_adjoin_singleton x.2)
  haveI : IsLocalRing S := by
    obtain ⟨q, hq⟩ := Ideal.exists_maximal S
    have e : S ≃+* Localization.AtPrime q := RingEquiv.ofBijective (algebraMap _ _)
      ⟨IsLocalization.injective _ q.primeCompl_le_nonZeroDivisors,
        GlobalTheory.surjective_algebraMap_localization_of_henselian O q⟩
    exact e.symm.isLocalRing
  have hle : S ≤ (integralClosure O Ω) :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 x.2)
  let f : S →+* integralClosure O Ω := (Subalgebra.inclusion hle).toRingHom
  have hx : f ⟨x, Algebra.self_mem_adjoin_singleton O _⟩ = x := rfl
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (⟨x, Algebra.self_mem_adjoin_singleton O _⟩ : S) with h | h
  · left; simpa [hx] using h.map f
  · right; simpa [hx] using h.map f

variable (O : Type) [CommRing O] [HenselianLocalRing O] (K : Type) [Field K] [Algebra O K]
  (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra O Ω] [IsScalarTower O K Ω]

instance : IsLocalRing (integralClosure O Ω) := isLocalRing_integralClosure O Ω

variable {Ω}

variable {O K}

variable (O K Ω)

end Ring
end GlobalTheory.EtC.Psi

namespace GlobalTheory.EtC.Psi
open GlobalTheory.EtC.Rel

section Schemes

variable {O : Type} [CommRing O] [HenselianLocalRing O] (K : Type) [Field K] [Algebra O K]
  (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra O Ω] [IsScalarTower O K Ω]
  {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O))

variable {K Ω}

end Schemes
end GlobalTheory.EtC.Psi

namespace GlobalTheory.EtC.Psi
open GlobalTheory.EtC.Rel

section Nearby

variable (R : Type) [CommRing R]
variable {O : Type} [CommRing O] [HenselianLocalRing O] (K : Type) [Field K] [Algebra O K]
  (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra O Ω] [IsScalarTower O K Ω]
  {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O))

variable {K Ω}

end Nearby
end GlobalTheory.EtC.Psi

namespace GlobalTheory.EtC.Psi
open GlobalTheory.EtC.Rel

section Adic

variable (l : ℕ) [Fact l.Prime]

instance (X : Scheme.{0}) (L : DerivedCategory (ShvS ℤ_[l] X)) (n : ℤ) : Module ℤ_[l] (HX ℤ_[l] X L n) :=
  Module.compHom _ (ULift.ringEquiv.symm : ℤ_[l] ≃+* ULift.{1} ℤ_[l]).toRingHom

variable {O : Type} [CommRing O] [HenselianLocalRing O] (K : Type) [Field K] [Algebra O K]
  (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra O Ω] [IsScalarTower O K Ω]
  {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O))

end Adic
end GlobalTheory.EtC.Psi

namespace GlobalTheory.EtC.Psi
open GlobalTheory.EtC.Rel

section AdicGal

variable (R : Type) [CommRing R]
variable {O : Type} [CommRing O] [HenselianLocalRing O] {K : Type} [Field K] [Algebra O K]
  {Ω : Type} [Field Ω] [Algebra K Ω] [Algebra O Ω] [IsScalarTower O K Ω]
  {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O))

end AdicGal
end GlobalTheory.EtC.Psi

namespace GlobalTheory.EtC.Psi
open GlobalTheory.EtC.Rel

section Examples

variable (R : Type) [CommRing R] (O : Type) [CommRing O] [HenselianLocalRing O] (K : Type) [Field K] [Algebra O K]
  (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra O Ω] [IsScalarTower O K Ω]

end Examples

end GlobalTheory.EtC.Psi
