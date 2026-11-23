module

public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

def GamAt {D : D7} (T : Top D) : Prop :=
  ∀ (j : ℕ) (_hj : InR D j) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp)
    (γ : GL (Fin D.R.r) D.host.E), IsUStab ((T.U j σ).X k).Gm ((T.U j σ).X k).Λ γ →
    (∀ x ∈ ((T.U j σ).X k).Λ, ∃ y ∈ ((T.U j σ).X k).Λ,
      Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) x - x = (T.Q.l.M : D.host.E) • y) →
    γ ∈ ((T.U j σ).X k).Γ

def HalfDiffNormSt : Prop :=
  ∀ D : D7, 0 < Ideal.absNorm D.host.𝔟 ∧
    2 * Real.log (Ideal.absNorm D.host.𝔟 : ℝ) ≤ Real.log |((NumberField.discr D.host.E : ℤ) : ℝ)|

end ReciprocityTheory.ChartRestriction.G.PullbackSections
