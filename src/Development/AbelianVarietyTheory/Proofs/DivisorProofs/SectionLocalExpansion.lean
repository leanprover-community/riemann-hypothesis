module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecOfSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixTransvectionDiagonalDecomposition
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem _root_.GlobalTheory.T.section_local_expansion : ∀ (Rg : Type) [CommRing Rg] (A₀ X : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (M : LB A₀) (Q : GlobalTheory.AbLaw.Perf f M) (s : LB.Sec M) (φ : X ⟶ A₀) (z : X) (i : Q.I), φ z ∈ Q.W i → gs φ z (M.U (Q.ch i)) (s.f (Q.ch i)) = ∑ k, gs φ z ⊤ (GlobalTheory.FormsLocus.cstT f (GlobalTheory.FormsLocus.vecOf Q s k)) * gs φ z (Q.W i) (Q.u k i) := by
  first | (exact @GlobalTheory.FormsLocus.VecGerm.germ_eq_sum_vecOf) | (exact GlobalTheory.FormsLocus.VecGerm.germ_eq_sum_vecOf) | (intros; apply GlobalTheory.FormsLocus.VecGerm.germ_eq_sum_vecOf <;> assumption)
