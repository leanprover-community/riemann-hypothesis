module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaStepSplitPlaceValuePeriodGroupInvaria
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.doubleThetaStep_splitPlace_value_periodGroup_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) c₁ c₂, Q.Away c₁ → Q.Away c₂ → ∀ f₁ f₂, Q.Vac f₁ f₂ → ∀ φ f, IsContAut S.B.A φ → IsContAut S.B'.V f → Q.Typed f → ∀ g h₁ h₂, g ∈ GlobalTheory.FinPl.grpOff S.B.V (· = Q.q.v) → h₁ ∈ GlobalTheory.FinPl.grpOff S.J.W (· = Q.q.v) → h₂ ∈ GlobalTheory.FinPl.grpOff S.B'.V (· = Q.q.v) → ∀ a x y, ∀ r ∈ RFJ Q.k Q.n₁ (Q.c + 1 + 1) (σ + 1), ∀ j ∈ Q.L₁.J, ∀ r' ∈ R Q.k Q.n₂ (Q.c + 1) (σ + 1), ∀ j' ∈ Q.L₂.J, S.val c₁ c₂ (comb ψ _ _ Q.D₁ f₁) (comb ψ _ _ Q.D₂ f₂) φ f (g * Q.gl₀ a) (h₁ * Q.gl₁ (r * x * j)) (h₂ * Q.gl₂ (r' * y * j')) = S.val c₁ c₂ (comb ψ _ _ Q.D₁ f₁) (comb ψ _ _ Q.D₂ f₂) φ f (g * Q.gl₀ a) (h₁ * Q.gl₁ x) (h₂ * Q.gl₂ y) := by
  exact @GlobalTheory.DblInv.val_inv
