module

public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockActionDiagonalCoefficientSpaceSmul
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass

@[expose] public section

open Formalism.L2.Ker MvPolynomial

theorem _root_.GlobalTheory.T.blockAction_diagonal_coefficientSpace_smul : ∀ {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n) (c : ι → ℂ) (Q : Formalism.L2.DIV.Pol ℂ ι n), Q ∈ Formalism.L2.DIV.VV ℂ lam → Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => Matrix.diagonal fun _ : Fin n => c τ) Q = (∏ τ, c τ ^ ∑ a, (lam τ).natW a) • Q := by
  first | exact @GlobalTheory.blockAct_diag_mem_VV | exact GlobalTheory.blockAct_diag_mem_VV | (intros; apply GlobalTheory.blockAct_diag_mem_VV <;> assumption)
