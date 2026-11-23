module

public import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.GaussJetBounds.OneLetterGaussJets.OddLevelGainSum
import Formalism.GaussJetBounds.StatementH

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped BigOperators

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds Formalism.IncomingBounds

section Final

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df1 : DefSide Bs}

def LocalValuationBoundAt (Dc : DefCols Df1) (u : Dc.Mem) (t : Bs.Tup) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K))
    (w : HeightOneSpectrum (𝓞 K)) (sgw : ℝ) : Prop :=
  ∀ φ ∈ Nu, ∀ F ∈ Df1.Mt t, Dc.Pt u t φ F = 0 ∨ sgw ≤ (vw w (Dc.Pt u t φ F) : ℝ)

end Final

end Formalism.L2.DIV
