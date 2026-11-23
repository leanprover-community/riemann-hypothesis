module

public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmallPointsSubstitutionAlgHomSinglePoint
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymmetricLiftOrderSymmetryMultiplicativity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit

theorem _root_.GlobalTheory.T.symmetricLift_order_symmetry_multiplicativity : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S), Function.Surjective (t.G ⊗ t.G).hom.appTop.hom → ∀ (wP : PrimTyG t), wP.IsGen → ∀ (k : ℕ) (a : baseOver S ⟶ t.G) (U : ThetaGrp t.G t.PP.L (k : ℤ) (baseOver S)), SymLift t.G t.PP.L (k : ℤ) k a U → ∀ (T : Over S) (σ : T ⟶ baseOver S) (z : T.left) (J : (T.left ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → LiftLaws (cubV t.cub z J) (fun p : T ⟶ t.G => val wP p.left z J) (fun p : T ⟶ t.G => GlobalTheory.CommPairing.tval U (lift σ p).left z J) (fun p : T ⟶ t.G => p ≫ t.act.act H.w0) (σ ≫ a) k := by
  first | exact @GlobalTheory.TransUnit.liftLaws_of_symLift | exact GlobalTheory.TransUnit.liftLaws_of_symLift | (intros; apply GlobalTheory.TransUnit.liftLaws_of_symLift <;> assumption)
