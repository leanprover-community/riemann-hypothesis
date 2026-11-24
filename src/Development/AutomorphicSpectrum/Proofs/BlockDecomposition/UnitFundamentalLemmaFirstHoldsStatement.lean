module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitFundamentalLemmaFirstHolds
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section


theorem _root_.GlobalTheory.T.unit_fundamental_lemma_first_holds : PositivityTheory.Rg.Tf.Loc.D0a → PositivityTheory.Rg.Tf.Loc.T0 → PositivityTheory.Rg.Tf.Loc.A1 → PositivityTheory.Rg.Tf.Loc.A2 → PositivityTheory.Rg.Tf.Loc.A3 → PositivityTheory.Rg.Tf.Loc.N4 → PositivityTheory.Rg.Tf.Loc.L2 → PositivityTheory.Rg.Tf.Loc.L3 → PositivityTheory.Rg.Tf.Loc.L4 → PositivityTheory.Rg.Tf.Loc.H2 → PositivityTheory.Rg.Tf.Loc.H3 → PositivityTheory.Rg.Tf.Loc.H4 → PositivityTheory.Rg.Tf.Loc.Z1 := by
  first | exact @GlobalTheory.CompanionTheory.UnitFL.unit_fundamental_lemma_first | exact GlobalTheory.CompanionTheory.UnitFL.unit_fundamental_lemma_first | (intros; apply GlobalTheory.CompanionTheory.UnitFL.unit_fundamental_lemma_first <;> assumption)
