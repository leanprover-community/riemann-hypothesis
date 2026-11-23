module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceDoubleStepFlatContractionExpand
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagGenDiag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowBesZeroE
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitPlace_doubleStep_flatContraction_expand : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), GlobalTheory.SplitWeil.IsUnitVol ν → ∀ (p : GlobalTheory.LocMod.Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ψk : AddChar k Circle), p.IsChar ψ ψk → GlobalTheory.SplitWeil.HasConductor ψk 1 → ∀ (σ : ℕ) (B : GlobalTheory.Unf.BesLev D (σ + 1)) (J : GlobalTheory.Unf.JacLev D (σ + 1)) (B' : GlobalTheory.Unf.BesLev D σ) (n₀ : Type) [Fintype n₀] [DecidableEq n₀] (n₁ : Type) [Fintype n₁] [DecidableEq n₁] (n₂ : Type) [Fintype n₂] [DecidableEq n₂] (c : ℕ) (F : GlobalTheory.LocMod.Dbl p B J B' n₀ n₁ n₂ c) (s₁ : GlobalTheory.Unf.StepBF ψ B J) (s₂ : GlobalTheory.Unf.StepFB ψ J B') (l : GlobalTheory.Unf.Link B B'.L B'.ζ) (vL : GlobalTheory.Unf.VolM D B'.L.rank J.W₀.rank) T₁ T₂, p.IsModel ψ F.G₀ F.G₁ T₁ → p.IsModel ψ F.G₁ F.G₂ T₂ → ∀ Φ₁ Φ₂ O₁ O₂, GlobalTheory.LocMod.IsOne O₁ → GlobalTheory.LocMod.IsOne O₂ → ∀ (I : Type) (S : Finset I) (x : I → ℂ) (Ξ₁ : I → GlobalTheory.SplitWeil.SB (Matrix n₁ n₀ k)) (Ξ₂ : I → GlobalTheory.SplitWeil.SB (Matrix n₂ n₁ k)) (c₁ : I → WO B.A J.W₀ →₀ ℂ) (c₂ : I → WO J.W₀ B'.A →₀ ℂ), (∀ i ∈ S, p.IsCombAt ψ F.F₀ F.F₁ (c₁ i) (Ξ₁ i).1 ∧ p.IsCombAt ψ F.F₁ F.F₂ (c₂ i) (Ξ₂ i).1) → (∀ q, GlobalTheory.LocFlat.contr ψk ν (GlobalTheory.LocFlat.flCol ψk ν (σ + 1 + 1) Φ₁.1) (GlobalTheory.LocFlat.flRow ψk ν (σ + 1) Φ₂.1) q = ∑ i ∈ S, x i * ((Ξ₁ i).1 q.1 * (Ξ₂ i).1 q.2)) → GlobalTheory.Unf.contr l J.W₀ vL (GlobalTheory.Unf.flatBF s₁ (T₁ Φ₁)) (GlobalTheory.Unf.flatFB s₂ (T₂ Φ₂)) = ∑ i ∈ S, x i • biComb ψ B.A J.W₀ B'.A (c₁ i) (c₂ i) (GlobalTheory.Unf.contr l J.W₀ vL (GlobalTheory.Unf.flatBF s₁ (T₁ O₁)) (GlobalTheory.Unf.flatFB s₂ (T₂ O₂))) := by
  first | exact @GlobalTheory.DblStepLoc.contr_flat_expand | exact GlobalTheory.DblStepLoc.contr_flat_expand | (intros; apply GlobalTheory.DblStepLoc.contr_flat_expand <;> assumption)
