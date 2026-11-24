module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowSideCardEqOfCoord
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR
namespace GlobalTheory.Fc.Ind
theorem base_level_rows_eq_dimension_alt : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c), _root_.GlobalTheory.Fc.Ind.summandDegreeZero D O c b := by
  intro D O c b
  have h1 : D.what₂.D0 = b.P.S0.D := GlobalTheory.rowSide_card_eq_of_coord O.ex.p0.s D.what₂.onb0 b.P.I.eRR0
  have key : ∀ (Z Z' : DefSub b.P.A3.fam3.amb3) (S : IndefData (b.P.A3.side3 b.P.P0 b.P.ψ0 Z))
      (S' : IndefData (b.P.A3.side3 b.P.P0 b.P.ψ0 Z')), Z = Z' → HEq S S' → S.D = S'.D := by
    intro Z Z' S S' h h'
    subst h
    cases eq_of_heq h'
    rfl
  have h2 := key _ _ _ _ b.B.Q.zs b.B.Q.s0
  have h3 := b.B.Q.zs
  unfold _root_.GlobalTheory.Fc.Ind.summandDegreeZero
  rw [h1, ← h2, ← h3]
  rfl
end GlobalTheory.Fc.Ind
end
