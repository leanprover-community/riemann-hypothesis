module

public import Formalism.PeriodIntegrals.CharIdem
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open CategoryTheory

namespace PI.CharIdemW

open PI.CharIdem

def Central : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (V : FDRep ℂ G) (x : MonoidAlgebra ℂ G),
    charIdem V * x = x * charIdem V

def Scalar : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (V W : FDRep ℂ G), Simple V → Simple W →
    (Nonempty (V ≅ W) → act W (charIdem V) = 1) ∧
    (IsEmpty (V ≅ W) → act W (charIdem V) = 0)

def MulEq : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (V W : FDRep ℂ G), Simple V → Simple W →
    (Nonempty (V ≅ W) → charIdem V * charIdem W = charIdem W) ∧
    (IsEmpty (V ≅ W) → charIdem V * charIdem W = 0)

theorem charIdem_of (hC : Central) (hS : Scalar) (hM : MulEq) : PI.CharIdem.CharIdem := by
  intro G _ _ V W hV hW
  refine ⟨(hS G V V hV hV).1 ⟨Iso.refl V⟩, (hS G V W hV hW).2, ?_, hC G V, (hM G V W hV hW).2⟩
  exact (hM G V V hV hV).1 ⟨Iso.refl V⟩

end PI.CharIdemW
