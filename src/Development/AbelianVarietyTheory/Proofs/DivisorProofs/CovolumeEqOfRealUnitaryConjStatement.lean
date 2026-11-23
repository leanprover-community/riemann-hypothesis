module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeEqOfRealUnitaryConj
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq

@[expose] public section

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

theorem _root_.GlobalTheory.T.covolume_eq_of_realUnitary_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (hΨ : X'.Ψ = X.Ψ) (u : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (x0 : Frame X.Ψ r) (x0' : Frame X'.Ψ r) (FF : Set (V (nd X))) (FF' : Set (V (nd X'))), X'.Gm = X.Gm → X'.p0 = X.p0 → (∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) → (∀ γ ∈ X.Γ, ∃ γ' ∈ X'.Γ, ∀ τ ∈ X.Ψ, u τ * (γ : Matrix (Fin r) (Fin r) E).map τ = (γ' : Matrix (Fin r) (Fin r) E).map τ * u τ) → (∀ γ' ∈ X'.Γ, ∃ γ ∈ X.Γ, ∀ τ ∈ X.Ψ, u τ * (γ : Matrix (Fin r) (Fin r) E).map τ = (γ' : Matrix (Fin r) (Fin r) E).map τ * u τ) → IsOrth X x0 → IsOrth X' x0' → IsFundSet X x0 FF → IsFundSet X' x0' FF' → muF X x0 FF = muF X' x0' FF' := by
  first | exact @GlobalTheory.CovolConj.muF_eq_of_conj | exact GlobalTheory.CovolConj.muF_eq_of_conj | (intros; apply GlobalTheory.CovolConj.muF_eq_of_conj <;> assumption)
