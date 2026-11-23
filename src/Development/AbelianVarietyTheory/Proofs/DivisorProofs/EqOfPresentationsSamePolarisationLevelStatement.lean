module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfPresentationsSamePolarisationLevel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.eq_of_presentations_same_polarisation_level : ∀ {o : Type} [CommRing o] {ζ : o} {h n : ℕ} (F' : SFam h n ζ), 3 ≤ n → IsUnit ζ → IsUnit (n : o) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (A : Over (Sp V)) [GrpObj A] [IsCommMonObj A] (t₁ t₂ : Sp V ⟶ F'.X) (a₁ a₂ : A.left ⟶ F'.univ.A.left) (aa₁ aa₂ : (G2 A).left ⟶ (G2 F'.univ.A).left), IsGrpPullback A F'.univ.A t₁ a₁ → IsGrpPullback A F'.univ.A t₂ a₂ → IsSquare a₁ aa₁ → IsSquare a₂ aa₂ → LBIso (F'.univ.P.pull aa₁) (F'.univ.P.pull aa₂) → t₁ ≫ F'.s = t₂ ≫ F'.s → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F], (∀ l, ∃ x : TF (R := V) F ⟶ A, x.left ≫ a₁ = (TF (R := V) F).hom ≫ t₁ ≫ (F'.univ.lev l).left ∧ x.left ≫ a₂ = (TF (R := V) F).hom ≫ t₂ ≫ (F'.univ.lev l).left) → t₁ = t₂ ∧ a₁ = a₂ := by
  first | exact @GlobalTheory.LowSame.eq_of_presentations | exact GlobalTheory.LowSame.eq_of_presentations | (intros; apply GlobalTheory.LowSame.eq_of_presentations <;> assumption)
