module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosVec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiBalanceFormalSumMemSpanCubicalTheta
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.rosatiBalanceFormalSum_mem_span_cubicalTheta : ∀ {r : ℕ} (W A A' : Matrix (Fin r) (Fin r) ℤ), A.transpose * (W + W.transpose) = (W + W.transpose) * A' → GlobalTheory.TensBal.sig W A A' ∈ Submodule.span ℤ (Set.range fun p : GlobalTheory.TensBal.Vec r × GlobalTheory.TensBal.Vec r × GlobalTheory.TensBal.Vec r => GlobalTheory.TensBal.theta p.1 p.2.1 p.2.2) := by
  first | exact @GlobalTheory.TensBal.SpanPf.main | exact GlobalTheory.TensBal.SpanPf.main | (intros; apply GlobalTheory.TensBal.SpanPf.main <;> assumption)
