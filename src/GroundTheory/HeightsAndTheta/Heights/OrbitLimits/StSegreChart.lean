module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StokesObjects
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar ptsIntegral pot segre PBlk oneLine
  isSmoothHerm_oneLine)

def SegreChart.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (u v : ((Σ k, ι k) → ℂ) → ℝ)
    (i : (k : K) → ι k) (δ : ℝ),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsDegZeroSmooth u → IsDegZeroSmooth v →
    0 < δ → (∀ z, ‖segre z i‖ < δ * ‖segre z‖ → u z = 0) →
      ∃ (m : ℕ) (Js : Finset (Ideal (MvPolynomial (Fin m) ℂ))) (U V : (Fin m → ℂ) → ℝ)
        (Φ : Fin n → (Fin m → ℂ) → ℝ),
        (∀ J ∈ Js, J.IsPrime ∧ ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (n + 1 : ℕ) ∧
          SmoothNear (ComplexSets.zeroSet J) U ∧ SmoothNear (ComplexSets.zeroSet J) V ∧
          ∀ j, SmoothNear (ComplexSets.zeroSet J) (Φ j)) ∧
        HasCompactSupport U ∧
        ptsIntegral P (Fin.cons v (pot L)) u = ∑ J ∈ Js, varInt J (n + 1) U (Matrix.vecCons V Φ) ∧
        ptsIntegral P (Fin.cons u (pot L)) v = ∑ J ∈ Js, varInt J (n + 1) V (Matrix.vecCons U Φ)

end GroundTheory.Heights₂.Heights
