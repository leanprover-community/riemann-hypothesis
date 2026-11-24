module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
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
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.TwistedIndependenceLemma.TwistedIndependence

@[expose] public section

noncomputable section

open GlobalTheory.PRep Formalism.UG NumberField IsDedekindDomain PositivityTheory.Lbc
open scoped Pointwise

namespace PositivityTheory.SphericalProduct

section Lat

variable (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def latK (n k : ℕ) : Set (Fin n → L) :=
  {x | ∀ i : Fin n, if i.val < k then Valued.v (x i) ≤ 1 else Valued.v (x i) < 1}

def IwGL (n : ℕ) : Subgroup (GL (Fin n) L) :=
  ⨅ k : Fin (n + 1), (MulAction.stabilizer (LinearMap.GeneralLinearGroup L (Fin n → L)) (latK L n k)).comap
    (Matrix.GeneralLinearGroup.toLin : GL (Fin n) L ≃* _).toMonoidHom

variable {L}

def IsDiagM {n : ℕ} (g : GL (Fin n) L) : Prop := ∀ i j : Fin n, i ≠ j → (g : Matrix (Fin n) (Fin n) L) i j = 0

def IsUniM {n : ℕ} (g : GL (Fin n) L) : Prop :=
  (∀ i j : Fin n, j < i → (g : Matrix (Fin n) (Fin n) L) i j = 0) ∧ ∀ i : Fin n, (g : Matrix (Fin n) (Fin n) L) i i = 1

def IsStrictDom {n : ℕ} (g : GL (Fin n) L) : Prop :=
  ∀ i j : Fin n, i < j → ordL ((g : Matrix (Fin n) (Fin n) L) j j) < ordL ((g : Matrix (Fin n) (Fin n) L) i i)

end Lat

def jacSub {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (N : G → Prop) :
    Submodule ℂ V :=
  Submodule.span ℂ {y | ∃ u, N u ∧ ∃ v, y = ρ u v - v}

section U

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def IwU (σ : L →+* L) (n : ℕ) : Subgroup (GU σ n) := (IwGL L n).subgroupOf (GU σ n)

def ExtremeU : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) (α : Fin (n / 2) → ℂˣ),
    IsUnramInv ϖ σ q → IsAdmissible ρ → ρ.IsIrreducible → GlobalTheory.LFun.HasSatU ϖ q ρ α →
    ∃ β : Fin (n / 2) → ℂˣ, GlobalTheory.LGrp.WeylConjU α β ∧ (∀ i j : Fin (n / 2), i ≤ j → ‖(β j : ℂ)‖ ≤ ‖(β i : ℂ)‖) ∧
      (∀ i, 1 ≤ ‖(β i : ℂ)‖) ∧
      ∃ f : V →ₗ[ℂ] GlobalTheory.LFun.psSpaceU σ q β, Function.Injective f ∧
        ∀ (g : GU σ n) (v : V), f (ρ g v) = GlobalTheory.LFun.psFunU σ q β g (f v)

end U

section GeneralLinearIntegers

end GeneralLinearIntegers

end PositivityTheory.SphericalProduct

end
