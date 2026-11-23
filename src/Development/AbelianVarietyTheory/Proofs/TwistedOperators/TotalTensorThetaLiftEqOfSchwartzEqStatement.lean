module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TotalTensorThetaLiftEqOfSchwartzEq
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped Pointwise


theorem _root_.GlobalTheory.T.totalTensorThetaLift_eq_of_schwartz_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ {W : G.Weil} (M : Vol G) (ρ : RealMatch W) (t : T) {e : AE D}, IsIdemSum e (locPl G t) → GlobalTheory.FlipRun.CuspStep W M ρ t → ∀ {X Y : Node} (p : Path T X Y), GlobalTheory.FlipRun.OnGrid D.R.m t p → ∀ (τ₁ τ₂ : TotT G p) (φ₁ φ₂ : PureT G p → PureT G p), (∀ d ∈ τ₁.support, GlobalTheory.FlipRun.VecAll ρ e p (φ₁ d) d) → (∀ d ∈ τ₂.support, GlobalTheory.FlipRun.VecAll ρ e p (φ₂ d) d) → (∀ x : GlobalTheory.FlipRun.ArgT G p, GlobalTheory.FlipRun.HalfAll e p x → (τ₁.sum fun d c => c * GlobalTheory.FlipRun.famProd p (φ₁ d) x) = τ₂.sum fun d c => c * GlobalTheory.FlipRun.famProd p (φ₂ d) x) → ∀ F : Fn G X, GlobalTheory.FlipRun.IsCuspListed W.θ X F → ∀ Q : GlobalTheory.FlipRun.PolE G →₀ ℂ, liftT W M p (GlobalTheory.FlipRun.tensE W p Q τ₁) F = liftT W M p (GlobalTheory.FlipRun.tensE W p Q τ₂) F := by
  first | exact @GlobalTheory.FlipRun.liftT_tensE_eq_of_famProd | exact GlobalTheory.FlipRun.liftT_tensE_eq_of_famProd | (intros; apply GlobalTheory.FlipRun.liftT_tensE_eq_of_famProd <;> assumption)
