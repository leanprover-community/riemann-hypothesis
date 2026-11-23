module

public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseTransport
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeMackey
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory MonoidalCategory

universe u

noncomputable section

attribute [local instance 2000] Rep.hV2

section ZModRes

variable {G G' : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
  [TopologicalSpace G'] [IsTopologicalGroup G'] (θ : G ≃ₜ* G')

def zmodRepResIso (n : ℕ) : Rep.res θ.toMulEquiv.toMonoidHom (zmodRep.{u} G' n) ≅ zmodRep.{u} G n where
  hom := Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩
  inv := Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩



omit [IsTopologicalGroup G] [IsTopologicalGroup G'] in
theorem zmodMulPairingRight_res (n : ℕ) {D' : Rep.{u} (ULift.{u} ℤ) G'} {D : Rep.{u} (ULift.{u} ℤ) G}
    (hD' : ∀ d : D', n • d = 0) (hD : ∀ d : D, n • d = 0) (f : Rep.res θ.toMulEquiv.toMonoidHom D' ⟶ D) :
    (Rep.resFunctor θ.toMulEquiv.toMonoidHom).map (zmodMulPairingRight n D' hD') ≫ f =
      resTensorHom θ.toMulEquiv.toMonoidHom f (zmodRepResIso θ n).hom ≫ zmodMulPairingRight n D hD := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply TensorProduct.ext'
  intro d a
  obtain ⟨a⟩ := a
  change f.hom ((zmodMulPairing n D' hD').hom ((ULift.up a : zmodRep.{u} G' n) ⊗ₜ[ULift.{u} ℤ] (d : D') :
      (zmodRep.{u} G' n ⊗ D' : Rep _ _))) =
    (zmodMulPairing n D hD).hom ((ULift.up a : zmodRep.{u} G n) ⊗ₜ[ULift.{u} ℤ] f.hom d :
      (zmodRep.{u} G n ⊗ D : Rep _ _))
  rw [zmodMulPairing_tmul, zmodMulPairing_tmul]
  exact map_zsmul f.hom.toLinearMap.toAddMonoidHom _ _

end ZModRes

section Mackey

variable {F L Ω : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] [IsGalois F Ω] [IsGalois L Ω]
  {S : Set (HeightOneSpectrum (𝓞 F))}
  (hL : ∀ x : L, algebraMap L Ω x ∈ maxUnramifiedOutside F Ω S)
  (ιs : ∀ v : S, Ω →ₐ[F] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F))

def gsMackeyEmbeddings : ∀ w : (placesOver S : Set (HeightOneSpectrum (𝓞 L))),
    Ω →ₐ[L] AlgebraicClosure ((w : HeightOneSpectrum (𝓞 L)).adicCompletion L) :=
  Equiv.piCongrLeft (fun w : (placesOver S : Set (HeightOneSpectrum (𝓞 L))) =>
      Ω →ₐ[L] AlgebraicClosure ((w : HeightOneSpectrum (𝓞 L)).adicCompletion L))
    (mackeyPlaceEquiv S hL ιs) (fun p => gsLocalEmbeddingOver hL ιs p.1 p.2.out)

omit [IsGalois L Ω] in
theorem gsMackeyEmbeddings_mackeyPlaceEquiv
    (p : MackeyIndex (gsOpenSubgroup S hL) (gsFinFamily S ιs)) :
    gsMackeyEmbeddings hL ιs (mackeyPlaceEquiv S hL ιs p) = gsLocalEmbeddingOver hL ιs p.1 p.2.out :=
  Equiv.piCongrLeft_apply_apply _ _ _ _


omit [NumberField F] [Algebra F Ω] [IsScalarTower F L Ω] [IsGalois F Ω] in
theorem gsFinFamily_apply_of_eq {ιs' : ∀ w : (placesOver S : Set (HeightOneSpectrum (𝓞 L))),
      Ω →ₐ[L] AlgebraicClosure ((w : HeightOneSpectrum (𝓞 L)).adicCompletion L)}
    {w : (placesOver S : Set (HeightOneSpectrum (𝓞 L)))}
    {ι₀ : Ω →ₐ[L] AlgebraicClosure ((w : HeightOneSpectrum (𝓞 L)).adicCompletion L)} (h : ιs' w = ι₀)
    (σ : Gal(AlgebraicClosure ((w : HeightOneSpectrum (𝓞 L)).adicCompletion L) /
      (w : HeightOneSpectrum (𝓞 L)).adicCompletion L)) :
    gsFinFamily (placesOver S) ιs' w σ = decompHomS _ (placesOver S) ι₀ σ := by
  rw [← h]
  rfl

theorem gsBaseChange_mackeyFamily_eq (p : MackeyIndex (gsOpenSubgroup S hL) (gsFinFamily S ιs))
    (σ : mackeyGroup (gsOpenSubgroup S hL) (gsFinFamily S ιs) p) :
    gsBaseChange S hL (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs) p σ) =
      gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs) (mackeyPlaceEquiv S hL ιs p)
        (gsMackeyLocalEquiv hL ιs p.1 p.2.out σ) := by
  exact (gsBaseChange_mackeyFamily hL ιs p σ).trans
    (gsFinFamily_apply_of_eq (gsMackeyEmbeddings_mackeyPlaceEquiv hL ιs p) _).symm

section Compact

variable {k : Type u} [CommRing k]

def gsMackeyCompactIso {A' : Rep.{u} k (galUnramifiedOutside L Ω (placesOver S))} [IsDiscreteRep A']
    {A : Rep.{u} k (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S))} [IsDiscreteRep A]
    (f : Rep.res (gsBaseChange S hL).toMulEquiv.toMonoidHom A' ≅ A) (n : ℕ) :
    compactCohomologyRes (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs)) A' n ≅
      compactCohomologyRes (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs)) A n :=
  compactTransportIso (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
    (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs)) (gsBaseChange S hL) (mackeyPlaceEquiv S hL ιs)
    (fun p => gsMackeyLocalEquiv hL ιs p.1 p.2.out) (gsBaseChange_mackeyFamily_eq hL ιs) f n

theorem gsMackeyCompactIso_hom {A' : Rep.{u} k (galUnramifiedOutside L Ω (placesOver S))} [IsDiscreteRep A']
    {A : Rep.{u} k (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S))} [IsDiscreteRep A]
    (f : Rep.res (gsBaseChange S hL).toMulEquiv.toMonoidHom A' ≅ A) (n : ℕ) :
    (gsMackeyCompactIso hL ιs f n).hom =
      compactTransport (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
        (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs)) (gsBaseChange S hL) (mackeyPlaceEquiv S hL ιs)
        (fun p => gsMackeyLocalEquiv hL ιs p.1 p.2.out) (gsBaseChange_mackeyFamily_eq hL ιs) f.hom n :=
  rfl

end Compact

section ZMod

theorem gsMackeyCompactIso_compactCupRes_zmod (n : ℕ)
    {D' : Rep.{u} (ULift.{u} ℤ) (galUnramifiedOutside L Ω (placesOver S))} [IsDiscreteRep D']
    {D : Rep.{u} (ULift.{u} ℤ) (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S))} [IsDiscreteRep D]
    (hD' : ∀ d : D', n • d = 0) (hD : ∀ d : D, n • d = 0)
    (f : Rep.res (gsBaseChange S hL).toMulEquiv.toMonoidHom D' ≅ D) {r s m : ℕ} (h : r + s = m)
    (y : compactCohomologyRes (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs)) D' r)
    (x : cohomology (zmodRep.{u} (galUnramifiedOutside L Ω (placesOver S)) n) s) :
    (gsMackeyCompactIso hL ιs f m).hom.hom (compactCupRes _ (zmodMulPairingRight n D' hD') h y x) =
      compactCupRes (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs)) (zmodMulPairingRight n D hD) h
        ((gsMackeyCompactIso hL ιs f r).hom.hom y)
        ((cohomologyMapAlong (gsBaseChange S hL).toMulEquiv.toMonoidHom
          (continuous_mulEquiv_toMonoidHom (gsBaseChange S hL)) (zmodRepResIso (gsBaseChange S hL) n).hom s).hom
          x) :=
  compactTransport_compactCupRes (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
    (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs)) (gsBaseChange S hL) (mackeyPlaceEquiv S hL ιs)
    (fun p => gsMackeyLocalEquiv hL ιs p.1 p.2.out) (gsBaseChange_mackeyFamily_eq hL ιs) f.hom
    (zmodRepResIso (gsBaseChange S hL) n).hom f.hom (zmodMulPairingRight n D' hD') (zmodMulPairingRight n D hD)
    (zmodMulPairingRight_res (gsBaseChange S hL) n hD' hD f.hom) h y x

end ZMod

end Mackey

end

end GroundTheory.ProfCoh
