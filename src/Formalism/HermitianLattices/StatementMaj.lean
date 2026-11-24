module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField

noncomputable section

namespace Formalism.HermitianLatticesTheory

section Maj

variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

def vecAt (b : Module.Basis ι K V) (v : InfinitePlace K) (x : V) : ι → ℂ :=
  fun i => v.embedding (b.repr x i)

def gramAt (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V) (v : InfinitePlace K) :
    Matrix ι ι ℂ :=
  Matrix.of fun i j => v.embedding (h (b i) (b j))

def IsFrame (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V) (v : InfinitePlace K)
    (X : Matrix ι ι ℂ) : Prop :=
  IsUnit X.det ∧ ∃ ε : ι → ℂ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
    X.conjTranspose * gramAt h b v * X = Matrix.diagonal ε

def fcoord (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x : V) : ι → ℂ :=
  Matrix.mulVec (X v)⁻¹ (vecAt b v x)

def cnorm (u : ι → ℂ) : ℝ := Real.sqrt (∑ i, ‖u i‖ ^ 2)

def normAt (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x : V) : ℝ :=
  cnorm (fcoord b X v x)

def majAt (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x y : V) : ℂ :=
  ∑ i, star (fcoord b X v x i) * fcoord b X v y i

theorem fcoord_add (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (x y : V) : fcoord b X v (x + y) = fcoord b X v x + fcoord b X v y := by
  unfold fcoord
  rw [← Matrix.mulVec_add]
  congr 1
  funext i
  simp [vecAt, map_add (f := _)]

theorem fcoord_zero (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) : fcoord b X v 0 = 0 := by
  have h0 : vecAt b v 0 = 0 := by
    funext i
    simp [vecAt]
  simp only [fcoord, h0, Matrix.mulVec_zero]

def realizeRaw (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) :
    V →+ (InfinitePlace K × ι × Fin 2 → ℝ) where
  toFun x p := if p.2.2 = 0 then (fcoord b X p.1 x p.2.1).re else (fcoord b X p.1 x p.2.1).im
  map_zero' := by
    funext p
    simp [fcoord_zero]
  map_add' := by
    intro x y
    funext p
    simp only [fcoord_add, Pi.add_apply]
    split_ifs <;> simp

def realize (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) :
    V →+ EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) :=
  (WithLp.linearEquiv 2 ℝ (InfinitePlace K × ι × Fin 2 → ℝ)).symm.toLinearMap.toAddMonoidHom.comp
    (realizeRaw b X)

variable [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]

def idealSmul (I : Submodule (RingOfIntegers K) K) (L : Submodule (RingOfIntegers K) V) :
    Submodule (RingOfIntegers K) V :=
  Submodule.span (RingOfIntegers K) {z | ∃ a ∈ I, ∃ x ∈ L, z = a • x}

def matAt (b : Module.Basis ι K V) (v : InfinitePlace K) (g : V →ₗ[K] V) : Matrix ι ι ℂ :=
  (LinearMap.toMatrix b b g).map v.embedding

end Maj

end Formalism.HermitianLatticesTheory
