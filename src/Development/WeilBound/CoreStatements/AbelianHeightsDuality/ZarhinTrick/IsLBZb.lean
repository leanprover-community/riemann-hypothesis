module

public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.PolQuasiInverse
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
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

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]

section Bundle

variable (mu : B ⟶ A) (α : Matrix (Fin 4) (Fin 4) ℤ) {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S)

def pA (i : Fin 4) : (Over.pullback s).obj (G4 (A ⊗ B)) ⟶ (Over.pullback s).obj A :=
  (Over.pullback s).map (prj (A ⊗ B) i ≫ fst A B)

def pM (i : Fin 4) : (Over.pullback s).obj (G4 (A ⊗ B)) ⟶ (Over.pullback s).obj A :=
  (Over.pullback s).map (prj (A ⊗ B) i ≫ snd A B ≫ mu)

def phiL : Fin 4 × Fin 4 → (((Over.pullback s).obj (G4 (A ⊗ B))).left ⟶ ((Over.pullback s).obj A).left)
  | (0, i) => (pA s i).left
  | (1, i) => (pA s i)⁻¹.left
  | (2, i) => (pM mu s i).left
  | (3, i) => (pM mu s i)⁻¹.left

def phiP (ij : Fin 4 × Fin 4) : ((Over.pullback s).obj (G4 (A ⊗ B))).left ⟶ (A ⊗ B).left :=
  (toBase (G4 (A ⊗ B)) s (𝟙 _) ≫ lift (prj (A ⊗ B) ij.1 ≫ fst A B) (prj (A ⊗ B) ij.2 ≫ snd A B)).left

def zb (P : LB (A ⊗ B).left) (L : LB ((Over.pullback s).obj A).left) :
    LB ((Over.pullback s).obj (G4 (A ⊗ B))).left :=
  tens (LB.LinComb L (phiL mu s) fun _ => 1) (LB.LinComb P (phiP s) fun ij => α ij.1 ij.2)

theorem isLB_zb {P : LB (A ⊗ B).left} (hP : P.IsLB) {L : LB ((Over.pullback s).obj A).left} (hL : L.IsLB) :
    (zb mu α s P L).IsLB :=
  isLB_tens (LB.isLB_linComb hL _ _) (LB.isLB_linComb hP _ _)

end Bundle

end PositivityTheory.PrwZar
