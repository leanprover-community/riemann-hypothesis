import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.SmoothNearbyCycles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictHenselisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingHomOfIsStrictHenselisation

section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

namespace GlobalTheory.FormalInv.Fib

variable {O : Type} [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω]

abbrev toBase {A : Type} [CommRing A] (g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of O)) (C : Type) [CommRing C]
    [Algebra A C] : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of O) :=
  Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ g

theorem toBase_comp {A : Type} [CommRing A] (g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of O)) {C B : Type}
    [CommRing C] [Algebra A C] [CommRing B] [Algebra A B] (u : C →ₐ[A] B) :
    Spec.map (CommRingCat.ofHom (u : C →+* B)) ≫ toBase g C = toBase g B := by
  rw [toBase, toBase, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]

abbrev fib {A : Type} [CommRing A] (g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of O)) (C : Type) [CommRing C]
    [Algebra A C] : Scheme.{0} :=
  GlobalTheory.NCyc.gfib Ω (toBase g C)

def fibMap {A : Type} [CommRing A] (g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of O)) {C B : Type}
    [CommRing C] [Algebra A C] [CommRing B] [Algebra A B] (u : C →ₐ[A] B) : fib Ω g B ⟶ fib Ω g C :=
  GlobalTheory.NCyc.gfibMap Ω (Spec.map (CommRingCat.ofHom (u : C →+* B))) (toBase_comp g u)

def fibStr {A : Type} [CommRing A] (g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of O)) (C : Type) [CommRing C]
    [Algebra A C] : fib Ω g C ⟶ GlobalTheory.NCyc.gfib Ω g :=
  GlobalTheory.NCyc.gfibMap Ω (Spec.map (CommRingCat.ofHom (algebraMap A C))) rfl



end GlobalTheory.FormalInv.Fib

end

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

namespace GlobalTheory.FormalInv.Tors

open GlobalTheory.FormalInv.Fib GlobalTheory.NCyc

variable {O : Type} [CommRing O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)]
variable (K : Type) [Field K] [Algebra O K] (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra O Ω] [IsScalarTower O K Ω]
variable [IsAlgClosed Ω] [FaithfulSMul O Ω] [Algebra.IsAlgebraic O Ω]
variable {X : Scheme.{0}} {p : X ⟶ Spec (CommRingCat.of O)} {x : SpecialPoint p}

end GlobalTheory.FormalInv.Tors

end
end

section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing GlobalTheory.FormalInv.Fib GlobalTheory.NCyc

namespace GlobalTheory.StrictHensFactor

theorem exists_factor_strictHenselisation : ∀ (A C B : Type) [CommRing A] [IsLocalRing A] [CommRing C] [Algebra A C] [CommRing B] [HenselianLocalRing B] [IsSepClosed (ResidueField B)] [Algebra A B] [IsLocalHom (algebraMap A B)] (u : C →ₐ[A] B), ∃ (D : Type) (_ : CommRing D) (_ : IsLocalRing D) (_ : Algebra A D) (c : C →ₐ[A] D) (w : D →ₐ[A] B), w.comp c = u ∧ ∃ (P : Ideal C) (_ : P.IsPrime) (φ : Localization.AtPrime P →+* D), GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ ∧ φ.comp (algebraMap C (Localization.AtPrime P)) = (c : C →+* D) ∧ P.comap (algebraMap A C) = maximalIdeal A := by
  intro A C B _ _ _ _ _ _ _ _ _ u
  set P : Ideal C := (maximalIdeal B).comap (u : C →+* B) with hP
  haveI hPp : P.IsPrime := Ideal.comap_isPrime _ _
  let L := Localization.AtPrime P
  have hu : ∀ y : P.primeCompl, IsUnit ((u : C →+* B) y) := by
    intro y
    have := y.2
    by_contra hy
    exact this ((IsLocalRing.mem_maximalIdeal _).2 hy)
  let b : L →+* B := IsLocalization.lift hu
  have hb : b.comp (algebraMap C L) = (u : C →+* B) := IsLocalization.lift_comp hu
  haveI hbloc : IsLocalHom b := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
    rw [IsLocalization.AtPrime.isUnit_mk'_iff]
    intro ha
    have h1 : (u : C →+* B) a = (u : C →+* B) s * b (IsLocalization.mk' _ a s) :=
      (IsLocalization.lift_mk'_spec _ _ _ _).1 rfl
    have h2 : IsUnit ((u : C →+* B) a) := by
      rw [h1]; exact (hu s).mul hx
    exact (IsLocalRing.mem_maximalIdeal _).1 ha h2
  obtain ⟨S, _, _, _, hloc, hsc, -, -, -, ι, _, _, _, Si, hmono, hcov, hA⟩ :=
    GlobalTheory.exists_strictHenselisation L (SeparableClosure (ResidueField L))
  have hind : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap L S) := by
    refine GlobalTheory.StrictHensUnion.indEtale_of_directed_union L S ι Si hmono hcov fun i => ?_
    obtain ⟨A', _, _, _, q, _, ⟨e⟩⟩ := hA i
    exact GlobalTheory.StrictHensUnion.indEtale_of_algEquiv e
      (GlobalTheory.StrictHensUnion.indEtale_localization_of_etale L A' q.primeCompl)
  have hstrict : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation (algebraMap L S) :=
    ⟨inferInstance, hsc, hloc, hind⟩
  obtain ⟨g, hg⟩ := GlobalTheory.NCyc.StrictLocLift.exists_ringHom_of_isStrictHenselisation
    (algebraMap L S) hstrict b
  let cR : C →+* S := (algebraMap L S).comp (algebraMap C L)
  letI algAS : Algebra A S := (cR.comp (algebraMap A C)).toAlgebra
  let c : C →ₐ[A] S := { cR with commutes' := fun a => rfl }
  have hgc : g.comp cR = (u : C →+* B) := by
    rw [← RingHom.comp_assoc, hg, hb]
  let w : S →ₐ[A] B :=
    { g with
      commutes' := fun a => by
        change g (cR (algebraMap A C a)) = algebraMap A B a
        rw [← RingHom.comp_apply, hgc]
        exact u.commutes a }
  refine ⟨S, inferInstance, inferInstance, algAS, c, w, ?_, P, hPp, algebraMap L S, hstrict, rfl, ?_⟩
  · ext x
    exact DFunLike.congr_fun hgc x
  · ext a
    rw [hP, Ideal.comap_comap, Ideal.mem_comap]
    have : ((u : C →+* B).comp (algebraMap A C)) a = algebraMap A B a := u.commutes a
    rw [this, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff, isUnit_map_iff]

end GlobalTheory.StrictHensFactor
end
