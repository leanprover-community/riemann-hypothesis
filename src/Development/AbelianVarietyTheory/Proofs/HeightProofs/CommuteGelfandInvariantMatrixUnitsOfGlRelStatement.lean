module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
public import Formalism.RealPlaceAnalysis.StatementA
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

theorem _root_.GlobalTheory.T.commute_gelfandInvariantMatrixUnits_of_glRel : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), Formalism.REAL.GlRel E → ∀ (k : ℕ) (a b : Fin n), E a b * gelfA E k = gelfA E k * E a b := by
  first | exact @GlobalTheory.SmoothForms.commute_gelfA | exact GlobalTheory.SmoothForms.commute_gelfA | (intros; apply GlobalTheory.SmoothForms.commute_gelfA <;> assumption)
