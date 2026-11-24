module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegOUnif
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
import Mathlib.Tactic.Lemma
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
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

def subSec {Y : Scheme.{0}} {M : LB Y} (s s' : LB.Sec M) : LB.Sec M where
  f j := s.f j - s'.f j
  compat i j := by rw [map_sub, map_sub, s.compat, s'.compat, mul_sub]

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

lemma fstG_act {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ) {G : Over (Spec (CommRingCat.of R))}
    (f : G ⟶ G) :
    ((Over.pullback (thick R I e)).map f).left ≫ (fstG I e G).left = (fstG I e G).left ≫ f.left := by
  simp only [fstG]
  simp

lemma pG_act {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) {O : Type} [Ring O] [StarRing O]
    [Module O D.toPre.X] {ιD : D.OAct O} {ιA : A.OAct O} {ιG : RingAct G O} (hlin : U.OLinear O ιD ιA ιG)
    (e : ℕ) (a : O) :
    ((Over.pullback (thick R I e)).map (ιG.act a)).left ≫ (U.gt e).pG.left =
      (U.gt e).pG.left ≫ (ιD.onB.act a).left := by
  have hq := congrArg (fun φ => φ.left) (hlin.q_lin e a)
  simp only [Over.comp_left] at hq
  unfold GtCoord.pG
  simp only [Over.comp_left, Over.map_map_left, Category.assoc]
  rw [← Category.assoc, hq, Category.assoc]
  congr 1
  first
    | exact fstG_act I e (ιD.onB.act a)


end ReciprocityTheory.ChartRestriction.G.DVR
