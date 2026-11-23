module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SpanSteps
public import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AlgebraMapOlInjective
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD TensorProduct

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)

def rdR {u : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j u) :=
  rdU (T.U j T.σ₀) F.1

def TieReadSt : Prop :=
  (∀ (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u) (k : (T.U j T.σ₀).Comp),
    rdR h j F k ∈ ((T.U j T.σ₀).X k).SS (laU (T.U j T.σ₀) (wtA u) u.n k)) ∧
  ∀ u : WeightFamilies.Wt D j, ReciprocityTheory.ChartRestriction.G.PullbackSections.JInjRd T j (wtA u) u.n

abbrev KT (T : Top D) (j N : ℕ) : Type := FractionRing (MvPolynomial (Idx D j N) T.Q.c.F)

def TieMaxCuspSt (CR Tt c : ℝ) (ka : WeightFamilies.Wt D j) : Prop :=
  ∀ F : (recB h.toLawsCore).Cusp j ka,
    F ∈ WeightFamilies.MggK (recB h.toLawsCore) CR Tt c j ka ↔
      ∀ k, rdR h j F k ∈ ((T.U j T.σ₀).X k).SSgt (laU (T.U j T.σ₀) (wtA ka) ka.n k) (WeightFamilies.c1 D CR Tt c j)

end Formalism.L2.Pj
