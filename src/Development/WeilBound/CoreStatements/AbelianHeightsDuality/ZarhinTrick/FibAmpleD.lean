module

public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.IsLBZb
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}}

def fourfoldProductLift {X G : Over S} (c : Fin 4 → (X ⟶ G)) : X ⟶ G4 G := lift (c 0) (lift (c 1) (lift (c 2) (c 3)))

variable {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

def eMap (mu : B ⟶ A) (α : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) : G4 (A ⊗ B) ⟶ G4 (A ⊗ B) :=
  fourfoldProductLift fun i => lift ((prj _ i ≫ fst A B) * (∏ j, (prj _ j ≫ snd A B ≫ mu) ^ (α i j))⁻¹)
    ((prj _ i ≫ snd A B) ^ (2 * m))

def eMap' (mu : B ⟶ A) (α : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) : G4 (A ⊗ B) ⟶ G4 (A ⊗ B) :=
  fourfoldProductLift fun i => lift ((prj _ i ≫ fst A B) ^ (2 * m) * ∏ j, (prj _ j ≫ snd A B ≫ mu) ^ (α i j))
    (prj _ i ≫ snd A B)

def lPart (mu : B ⟶ A) {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) :
    LB ((Over.pullback s).obj (G4 (A ⊗ B))).left :=
  LB.LinComb L (phiL mu s) fun _ => 1

end PositivityTheory.PrwZar
