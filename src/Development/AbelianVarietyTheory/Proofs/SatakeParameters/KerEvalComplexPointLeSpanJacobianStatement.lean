module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerEvalComplexPointLeSpanJacobian
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

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

theorem _root_.GlobalTheory.T.ker_evalComplexPoint_le_span_jacobian : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] (U : X.Opens), IsAffineOpen U →
    ∀ (ch : GlobalTheory.AlgChart p (RingHom.id ℂ) d) (φ : Fin d → Γ(X, U)) (z : GlobalTheory.CxPts p (RingHom.id ℂ))
      (_hzc : z ∈ ch.e.source) (hz : z ∈ GlobalTheory.CxPts.ptsIn p (RingHom.id ℂ) U), (ch.jacMat φ z).det ≠ 0 →
      RingHom.ker (GlobalTheory.CxPts.evHom hz) ≤
        Ideal.span (Set.range fun j => φ j - ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U (GlobalTheory.CxPts.evHom hz (φ j))) ⊔
          RingHom.ker (GlobalTheory.CxPts.evHom hz) ^ 2 := by
  first | (exact @GlobalTheory.JacSpan.ker_le_span_jac) | (exact GlobalTheory.JacSpan.ker_le_span_jac) | (intros; apply GlobalTheory.JacSpan.ker_le_span_jac  <;> assumption)
