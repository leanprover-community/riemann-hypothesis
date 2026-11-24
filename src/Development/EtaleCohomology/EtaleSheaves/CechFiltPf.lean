module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
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
import Mathlib.Tactic.Linter.Style
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.CechFiltPf

def Piece : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {E₀ E : Spc} (g : E₀ ⟶ E) (p : ℕ) (n : ℤ),
  Subsingleton (Hrel R (disc.map (g.app (op (SimplexCategory.mk p)))) F (n - p)) →
  Subsingleton (HK R (mappingCone ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map
    (((chains R).map g).f (-(p : ℤ))))) F n)

universe u v

theorem chains_isZero (R : Type) [CommRing R] (E : Spc) (j : ℤ) (hj : 0 < j) : IsZero (((chains R).obj E).X j) := by
  unfold chains
  exact HomologicalComplex.isZero_extend_X _ _ _ (fun i => by
    show -(i : ℤ) ≠ j
    omega)

theorem res_isZero (R : Type) [CommRing R] (F : Shv R) (j : ℤ) (hj : j < 0) : IsZero ((res R F).X j) := by
  unfold res InjectiveResolution.cochainComplex
  exact HomologicalComplex.isZero_extend_X _ _ _ (fun i => by
    show (i : ℤ) ≠ j
    omega)

def DiscLvl : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {P Q : PSh} (h : P ⟶ Q) (m : ℤ),
  Subsingleton (Hrel R (disc.map h) F m) →
  Subsingleton (HK R (mappingCone ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map h))) F m)

def ShiftLvl : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {E₀ E : Spc} (g : E₀ ⟶ E) (p : ℕ) (n : ℤ),
  Subsingleton (HK R (mappingCone ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map
    ((free R).map (g.app (op (SimplexCategory.mk p)))))) F (n - p)) →
  Subsingleton (HK R (mappingCone ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map
    (((chains R).map g).f (-(p : ℤ))))) F n)

theorem Piece_of (hD : DiscLvl) (hS : ShiftLvl) : Piece := by
  intro R _ F E₀ E g p n h
  exact hS R F g p n (hD R F _ _ h)

end LateralTheory.E.CechFiltPf
