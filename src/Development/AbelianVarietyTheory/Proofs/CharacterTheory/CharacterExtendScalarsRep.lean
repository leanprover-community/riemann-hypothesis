module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
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

open GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

def extendScalarsRep (K L : Type) [Field K] [Field L] [Algebra K L] {G : Type} [Group G] {n : ℕ}
    (ρ : Representation K G (Fin n → K)) : Representation L G (Fin n → L) where
  toFun g := Matrix.toLin' ((LinearMap.toMatrix' (ρ g)).map (algebraMap K L))
  map_one' := by
    rw [map_one, LinearMap.toMatrix'_one, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    rw [map_mul, LinearMap.toMatrix'_mul, Matrix.map_mul, Matrix.toLin'_mul]
    rfl

theorem character_extendScalarsRep (K L : Type) [Field K] [Field L] [Algebra K L] {G : Type}
    [Group G] {n : ℕ} (ρ : Representation K G (Fin n → K)) (g : G) :
    (extendScalarsRep K L ρ).character g = algebraMap K L (ρ.character g) := by
  have h1 : (extendScalarsRep K L ρ).character g
      = ((LinearMap.toMatrix' (ρ g)).map (algebraMap K L)).trace := by
    change LinearMap.trace L _ (Matrix.toLin' _) = _
    exact Matrix.trace_toLin'_eq _
  have h2 : ρ.character g = (LinearMap.toMatrix' (ρ g)).trace := by
    change LinearMap.trace K _ (ρ g) = _
    rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_toMatrix']
  rw [h1, h2]

  simp [Matrix.trace, map_sum]

theorem isChar_baseChange : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G]
    (χ : G → L), IsChar K L χ → IsChar L L χ := by
  intro K L _ _ _ G _ χ ⟨n, ρ, h⟩
  refine ⟨n, extendScalarsRep K L ρ, fun g => ?_⟩
  rw [h g, character_extendScalarsRep]
  rfl

end GlobalTheory.BI
