module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SqThD
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarCubeDerivWeierstrassPParameterSeriesBou
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl

theorem _root_.GlobalTheory.T.sigmaStarCubeDerivWeierstrassP_parameterSeries_bounded : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar →
    g3 g.abelian₂ ∈ Qbar → TaylorLogMetric.discr g.abelian₂ = 1 → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar →
      AlgEnt (sqThD g.abelian₂ v) ∧ ∃ w : PowerSeries ℂ_[p], BddSer w ∧
        g.atU (sqThD g.abelian₂ v) = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 * w := by
  first | exact @GlobalTheory.ThetaTransl.CubeSer.sqThD_atU | exact GlobalTheory.ThetaTransl.CubeSer.sqThD_atU | (intros; apply GlobalTheory.ThetaTransl.CubeSer.sqThD_atU <;> assumption)
