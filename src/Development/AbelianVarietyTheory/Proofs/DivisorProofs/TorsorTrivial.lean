module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyGenericOfKeyClosedPtsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorTrivialClosedPointsOfOriginClosedFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorTrivialGenericFibreOfStrictHenselClosedFibStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorTrivialStrictHenselisationOriginStatement
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

open scoped TensorProduct
open IsLocalRing Polynomial

namespace GlobalTheory.LocAcyc

theorem keyLocal_of (h1 : KeyClosedPts) (h2 : KeyGeneric) : KeyLocal := by
  intro T O _ _ _ _ _ _ _ _ hA P _ φ hφ hsh hP _ q hq hu
  by_cases h : P = (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T)
  · exact h2 T O hA P φ hφ hsh hP h q hq hu
  · exact h1 T O hA P φ hφ hsh hP h q hq hu

theorem torsor_trivial : ∀ (T O : Type) [CommRing T] [IsDomain T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O],
    (∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (D : Type) [CommRing D] [Algebra (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) D],
    Module.Finite (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) D → Module.Projective (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) D → Module.FaithfullyFlat (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) D →
    ∀ act : Multiplicative (ZMod q) →* (D ≃ₐ[(Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))] D),
    Function.Bijective (Algebra.TensorProduct.productMap
      (Pi.algHom (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) D))
      (Pi.algHom (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom))) →
    Nonempty (D →ₐ[(Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))] (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))) := by
  intro T O _ _ _ _ _ _ _ hA P _ φ hφ hsh q hq hu D _ _ hfin hproj hff act hbij
  have hO : KeyOrigin := GlobalTheory.T.torsor_trivial_strict_henselisation_origin
  have hAll : KeyAll :=
    GlobalTheory.T.torsorTrivialGenericFibre_of_strictHenselClosedFibre (keyLocal_of (GlobalTheory.T.torsorTrivialClosedPoints_of_origin_closedFibre hO) (GlobalTheory.T.keyGeneric_of_keyClosedPts' (GlobalTheory.T.torsorTrivialClosedPoints_of_origin_closedFibre hO)))
  exact hAll T O hA P φ hφ hsh q hq hu D hfin hproj hff act hbij

end GlobalTheory.LocAcyc
