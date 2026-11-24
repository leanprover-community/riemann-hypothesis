module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviModulusOneLinearReductiveExpMulExp
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification

@[expose] public section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

theorem _root_.GlobalTheory.T.leviModulusOne_linearReductive_exp_mul_exp : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Flag n a), IsIsoFlag ε j W → (∀ i, 1 ≤ j i) → GlobalTheory.LinRed.IsLinRed (mats (leviOne ε W)) ∧ ∀ g ∈ mats (leviOne ε W), ∃ X Y : Matrix (Fin n) (Fin n) ℂ, (∀ t : ℝ, NormedSpace.exp (t • X) ∈ mats (leviOne ε W)) ∧ (∀ t : ℝ, NormedSpace.exp (t • Y) ∈ mats (leviOne ε W)) ∧ g = NormedSpace.exp X * NormedSpace.exp Y := by
  first | exact @GlobalTheory.LeviPolar.isLinRed_leviOne | exact GlobalTheory.LeviPolar.isLinRed_leviOne | (intros; apply GlobalTheory.LeviPolar.isLinRed_leviOne <;> assumption)
