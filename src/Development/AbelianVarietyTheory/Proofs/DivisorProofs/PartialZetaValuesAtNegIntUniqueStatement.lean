module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaValuesAtNegIntUnique
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.partialZeta_values_at_neg_int_unique : ∀ {E : Type} [Field E] [NumberField E] {k : ℕ}, 2 ≤ k → ∀ {z z' : ClassGroup (GlobalTheory.CMVal.OF E) → ℚ}, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZetaVals k z → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsClassZetaVals k z' → z = z' := by
  first | exact @GlobalTheory.ZetaValUnique.classZetaVals_unique | exact GlobalTheory.ZetaValUnique.classZetaVals_unique | (intros; apply GlobalTheory.ZetaValUnique.classZetaVals_unique <;> assumption)
