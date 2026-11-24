module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase

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

def prj (G : Over S) : Fin 4 → (G4 G ⟶ G)
  | 0 => fst _ _
  | 1 => snd _ _ ≫ fst _ _
  | 2 => snd _ _ ≫ snd _ _ ≫ fst _ _
  | 3 => snd _ _ ≫ snd _ _ ≫ snd _ _

variable {A B : Over S} [GrpObj A] [GrpObj B]

def zcPair {P : LB (A ⊗ B).left} (hP : P.IsLB) (lm : A ⟶ B) (mu : B ⟶ A) (α : Matrix (Fin 4) (Fin 4) ℤ)
    {Y : Over S} (u u' : Y ⟶ G4 (A ⊗ B)) : Pic Y.left :=
  (∑ i, 2 • evc hP (u ≫ prj _ i ≫ fst A B) (u' ≫ prj _ i ≫ fst A B ≫ lm)) +
  (∑ i, ∑ j, α i j • (evc hP (u ≫ prj _ i ≫ fst A B) (u' ≫ prj _ j ≫ snd A B) +
      evc hP (u' ≫ prj _ i ≫ fst A B) (u ≫ prj _ j ≫ snd A B))) +
  (∑ i, 2 • evc hP (u ≫ prj _ i ≫ snd A B ≫ mu) (u' ≫ prj _ i ≫ snd A B ≫ mu ≫ lm))

def zc {P : LB (A ⊗ B).left} (hP : P.IsLB) (lm : A ⟶ B) (mu : B ⟶ A) (α : Matrix (Fin 4) (Fin 4) ℤ) :
    Pic (G4 (A ⊗ B) ⊗ G4 (A ⊗ B)).left :=
  zcPair hP lm mu α (fst _ _) (snd _ _)

end PositivityTheory.PrwZar
