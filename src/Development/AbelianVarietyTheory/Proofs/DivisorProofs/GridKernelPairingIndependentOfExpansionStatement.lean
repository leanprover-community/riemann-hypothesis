module

public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridKernelPairingIndependentOfExpansion
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

open Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj

theorem _root_.GlobalTheory.T.gridKernelPairing_independent_of_expansion : ∀ (D : D7) (T : Type) (L : LevCh D T) (sc : GlobalTheory.ChiGrid.Consts) (G : GridData L sc) (W : G.Weil) (U : Set T) (S : GridChoice W U) (μ₀ : T), L.Is μ₀ → ∀ t ∈ U, ∀ Φ : G.Datum, (∀ β τ, S.IsExpansion t Φ β τ → ∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) ∧ ∀ β τ τ', S.IsExpansion t Φ β τ → S.IsExpansion t Φ β τ' → ∀ c : S.Classes t Φ β, S.pairAt τ c = S.pairAt τ' c := by
  first | exact @GlobalTheory.FunObj.sumOK_vec_indep | exact GlobalTheory.FunObj.sumOK_vec_indep | (intros; apply GlobalTheory.FunObj.sumOK_vec_indep <;> assumption)
