module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivialIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFactorOfIndEtAtPrimeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleLiftGenericFibreOfFactorizationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFilteredColimitFiniteTypeIntRings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZmodTorsorModelOfFilteredColimitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorBaseChangeZmodStatement
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
import Mathlib.Data.Finset.Functor
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

open IsLocalRing Polynomial CategoryTheory Limits
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LocAcyc

theorem spread_torsor_to_etale : ∀ (T O : Type) [CommRing T] [CommRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O]
    (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale φ →
    ∀ (q : ℕ), 0 < q → ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib T O) D]
      (act : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib T O] D)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T O) D q act →
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra T E)
      (_ : IsScalarTower T (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E)
      (ψ : E →ₐ[Polynomial T] O) (DE : Type) (_ : CommRing DE)
      (_ : Algebra (GlobalTheory.LocAcyc.GenFib T E) DE)
      (actE : Multiplicative (ZMod q) →* (DE ≃ₐ[GlobalTheory.LocAcyc.GenFib T E] DE)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T E) DE q actE ∧
      ∀ s : DE →+* GlobalTheory.LocAcyc.GenFib T O,
        (∀ e : E, s (algebraMap (GlobalTheory.LocAcyc.GenFib T E) DE (algebraMap E _ e)) =
          algebraMap O (GlobalTheory.LocAcyc.GenFib T O) (ψ e)) →
        Nonempty (D →ₐ[GlobalTheory.LocAcyc.GenFib T O] GlobalTheory.LocAcyc.GenFib T O) := by
  intro T O _ _ _ _ _ P _ φ hφ hind q hq D _ _ act hD
  classical

  obtain ⟨j, Dj, _, _, actj, hDj, ⟨e⟩⟩ := GlobalTheory.T.exists_zmodTorsor_model_of_filtered_colimit _ _ _ (GlobalTheory.FiniteTypeColimit.isColimit
    (CommRingCat.of (GenFib T O))) q hq D act hD
  let U := (GlobalTheory.FiniteTypeColimit.diagram (CommRingCat.of (GenFib T O))).obj j
  let u : U →+* GenFib T O := ((GlobalTheory.FiniteTypeColimit.inclusions (CommRingCat.of (GenFib T O))).app j).hom
  haveI : Algebra.FiniteType ℤ U := GlobalTheory.FiniteTypeColimit.finiteType _ j

  have hfact := GlobalTheory.T.exists_etale_factorization_of_isIndEtale (Polynomial T) O P φ hφ hind
  have hl := GlobalTheory.T.exists_etale_lift_genericFibre_of_factorization T (Polynomial T) O hfact U u
  obtain ⟨W, _, _, _, _, _, ψ, uW, hcomp⟩ := hl
  letI : Algebra U (GenFib T W) := uW.toAlgebra
  obtain ⟨actE, hE⟩ := GlobalTheory.T.torsor_base_change_zmod U (GenFib T W) q Dj actj hq hDj
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ψ,
    TensorProduct U (GenFib T W) Dj, inferInstance, inferInstance, actE, hE, ?_⟩
  intro s hs
  have hs' : s.comp (algebraMap (GenFib T W) (TensorProduct U (GenFib T W) Dj)) =
      genFibMap (ψ.restrictScalars T) := by
    refine genFib_ringHom_ext (fun w => ?_)
    rw [RingHom.comp_apply, hs, genFibMap_algebraMap]
    rfl
  letI : Algebra U (GenFib T O) := u.toAlgebra
  let σ : Dj →ₐ[U] GenFib T O :=
    { s.comp (Algebra.TensorProduct.includeRight (R := U) (A := GenFib T W) (B := Dj)).toRingHom with
      commutes' := fun x => by
        change s (Algebra.TensorProduct.includeRight (algebraMap U Dj x)) = u x
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply U (GenFib T W)]
        rw [← RingHom.comp_apply s, hs', ← hcomp]
        rfl }
  let L : TensorProduct U (GenFib T O) Dj →ₐ[GenFib T O] GenFib T O :=
    Algebra.TensorProduct.lift (AlgHom.id (GenFib T O) (GenFib T O)) σ
      (fun _ _ => Commute.all _ _)
  exact ⟨L.comp e.symm.toAlgHom⟩

end GlobalTheory.LocAcyc
