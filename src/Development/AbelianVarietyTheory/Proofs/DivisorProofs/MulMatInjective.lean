module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField GlobalTheory.BCT Matrix
open scoped Classical

namespace GlobalTheory.TwLat

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ} (b : Module.Basis (Fin m) K.E B.A)

theorem mulMat_eq_map (a : B.A) :
    mulMat e b a = (e : K.E →+* w.adicCompletion E).mapMatrix (LinearMap.toMatrix b b (LinearMap.mulLeft K.E a)) := rfl

theorem mulMat_one : mulMat e b (1 : B.A) = 1 := by
  rw [mulMat_eq_map, LinearMap.mulLeft_one, LinearMap.toMatrix_id, map_one]

theorem mulMat_mul (a a' : B.A) : mulMat e b (a * a') = mulMat e b a * mulMat e b a' := by
  rw [mulMat_eq_map, mulMat_eq_map, mulMat_eq_map, LinearMap.mulLeft_mul, ← map_mul, ← LinearMap.toMatrix_mul]
  rfl

theorem mulMat_injective : Function.Injective (mulMat e b) := by
  intro a a' h
  have h1 : LinearMap.toMatrix b b (LinearMap.mulLeft K.E a) = LinearMap.toMatrix b b (LinearMap.mulLeft K.E a') :=
    Matrix.map_injective e.injective h
  have h2 := congrArg (fun f : B.A →ₗ[K.E] B.A => f 1) ((LinearMap.toMatrix b b).injective h1)
  simpa using h2

def mulU : B.Aˣ →* GLw m w where
  toFun a := ⟨mulMat e b a, mulMat e b ((a⁻¹ : B.Aˣ) : B.A),
    by rw [← mulMat_mul, Units.mul_inv, mulMat_one], by rw [← mulMat_mul, Units.inv_mul, mulMat_one]⟩
  map_one' := Units.ext (mulMat_one e b)
  map_mul' a a' := Units.ext (mulMat_mul e b _ _)

theorem mulU_val (a : B.Aˣ) : (mulU e b a).val = mulMat e b a := rfl

theorem mulU_injective : Function.Injective (mulU e b) :=
  fun _ _ h => Units.ext (mulMat_injective e b (congrArg Units.val h))

end GlobalTheory.TwLat
