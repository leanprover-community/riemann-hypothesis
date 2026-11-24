module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Data.Matrix.Mul
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
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting

@[expose] public section

noncomputable section

namespace GlobalTheory.VolAt

open Formalism.MainNotions.G Matrix

def homLat (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k k' : ℕ}
    (A : Submodule W (Fin k → Qq)) (B : Submodule W (Fin k' → Qq)) : Submodule W (Matrix (Fin k') (Fin k) Qq) where
  carrier := {x | ∀ z ∈ A, x *ᵥ z ∈ B}
  zero_mem' := fun z _ => by rw [Matrix.zero_mulVec]; exact B.zero_mem
  add_mem' := fun hx hy z hz => by rw [Matrix.add_mulVec]; exact B.add_mem (hx z hz) (hy z hz)
  smul_mem' := fun c x hx z hz => by
    rw [Matrix.smul_mulVec]
    exact B.smul_mem c (hx z hz)

theorem mem_homLat (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k k' : ℕ}
    (A : Submodule W (Fin k → Qq)) (B : Submodule W (Fin k' → Qq)) (x : Matrix (Fin k') (Fin k) Qq) :
    x ∈ homLat W A B ↔ ∀ z ∈ A, x *ᵥ z ∈ B := Iff.rfl

end GlobalTheory.VolAt
