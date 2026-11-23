module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageUpOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FerrandPushoutGoodBasicOpen
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem _root_.GlobalTheory.T.ferrand_pushout_good_basic_open : ∀ {Y₀ Y₁ Y₂ : Scheme.{0}} (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) [IsClosedImmersion i₁] [Surjective i₁] [IsClosedImmersion i₂] [Surjective i₂], ∀ U ∈ GlobalTheory.FerrandPush.good i₁ i₂, ∀ a : (GlobalTheory.FerrandPush.fib i₁ i₂).obj (op U), Y₀.basicOpen (((GlobalTheory.FerrandPush.fibπ i₁ i₂).app (op U)).hom a) ∈ GlobalTheory.FerrandPush.good i₁ i₂ := by
  first | exact @GlobalTheory.FerrandPush.basicOpen_fibπ_mem_good | exact GlobalTheory.FerrandPush.basicOpen_fibπ_mem_good | (intros; apply GlobalTheory.FerrandPush.basicOpen_fibπ_mem_good; all_goals assumption)
