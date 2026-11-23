module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DvdPowZeroIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramClassElementaryDivisorColumnsCongr
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.gramClass_elementaryDivisor_columns_congr : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (JT : GL (Fin n') L) (x y : Matrix (Fin n') (Fin n) L)
    (V : Matrix (Fin n) (Fin n) L) (a : Fin n → ℕ), (∀ i j, V i j ∈ Formalism.UG.intL L) →
    (∀ c : Fin n → L, (∀ j, c j ∈ Formalism.UG.intL L) →
      ((∀ i, (x *ᵥ (V *ᵥ c)) i ∈ Formalism.UG.intL L) ↔ ∀ j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a j) (c j))) →
    GlobalTheory.Hk3.HoweG.GramEq σ JT x y →
    ∀ i j : Fin n, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (min (a i) (a j))
      (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (y *ᵥ (V *ᵥ Pi.single i (ϖ ^ a i))) (y *ᵥ (V *ᵥ Pi.single j (ϖ ^ a j))) -
        Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (x *ᵥ (V *ᵥ Pi.single i (ϖ ^ a i))) (x *ᵥ (V *ᵥ Pi.single j (ϖ ^ a j)))) := by
  first | exact @GlobalTheory.Hk3.IntWitt.gram_class_columns | exact GlobalTheory.Hk3.IntWitt.gram_class_columns | (intros; apply GlobalTheory.Hk3.IntWitt.gram_class_columns <;> assumption)
