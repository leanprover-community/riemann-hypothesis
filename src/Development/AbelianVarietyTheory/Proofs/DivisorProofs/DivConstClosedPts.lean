module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
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

open IsLocalRing Polynomial

namespace GlobalTheory.VertUnits

def DivConst (T O : Type) [CommRing T] [CommRing O] [Algebra T O] : Prop :=
  ∀ (b c : O) (s : T), s ≠ 0 → b * c = algebraMap T O s →
    ∃ (a : T) (w : Oˣ), b = algebraMap T O a * (w : O)

def DivConstAll : Prop :=
  ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → DivConst T O

def DivConstWith (S : ∀ (T : Type) [CommRing T] [IsLocalRing T], Ideal (Polynomial T) → Prop) :
    Prop :=
  ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ →
    P.comap (Polynomial.C : T →+* Polynomial T) = maximalIdeal T → S T P → DivConst T O

def DivConstLocal : Prop := DivConstWith (fun _ _ _ _ => True)

def DivConstGeneric : Prop :=
  DivConstWith (fun T _ _ P => P = (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T))

def DivConstClosedPts : Prop :=
  DivConstWith (fun T _ _ P => P ≠ (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T))

def DivConstOrigin : Prop :=
  DivConstWith (fun T _ _ P =>
    P = (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) ⊔ Ideal.span {Polynomial.X})

theorem divConstLocal_of (h₁ : DivConstClosedPts) (h₂ : DivConstGeneric) : DivConstLocal := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP _
  by_cases hg : P = (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T)
  · exact h₂ T O hT P φ hφ hsh hP hg
  · exact h₁ T O hT P φ hφ hsh hP hg

end GlobalTheory.VertUnits
