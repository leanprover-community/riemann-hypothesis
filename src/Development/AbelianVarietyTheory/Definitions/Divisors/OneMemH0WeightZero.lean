module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Algebra.Quaternion
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped TensorProduct Quaternion

namespace GlobalTheory.QSA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def nrm {R : Type*} [CommRing R] {a b : R} (x : ℍ[R, a, b]) : R :=
  x.re ^ 2 - a * x.imI ^ 2 - b * x.imJ ^ 2 + a * b * x.imK ^ 2

def coords {R : Type*} [CommRing R] {a b : R} (x : ℍ[R, a, b]) : Fin 4 → R :=
  ![x.re, x.imI, x.imJ, x.imK]

scoped instance top {R : Type*} [CommRing R] [TopologicalSpace R] {a b : R} : TopologicalSpace ℍ[R, a, b] :=
  TopologicalSpace.induced coords inferInstance

variable (F : Type) [Field F] [NumberField F]

abbrev DA (a b : F) : Type := ℍ[AF F, algebraMap F (AF F) a, algebraMap F (AF F) b]

variable {F}

def rat {a b : F} (x : ℍ[F, a, b]) : DA F a b :=
  ⟨algebraMap F (AF F) x.re, algebraMap F (AF F) x.imI, algebraMap F (AF F) x.imJ, algebraMap F (AF F) x.imK⟩

def H0 {a b : F} (ε : AF F) : Set (DA F a b) :=
  {x | ∃ γ : ℍ[F, a, b], nrm γ = 1 ∧ ∃ h : DA F a b, nrm h = 1 ∧ ε • (h - 1) = h - 1 ∧ x = rat γ * h}

theorem nrm_mul {R : Type*} [CommRing R] {a b : R} (x y : ℍ[R, a, b]) : nrm (x * y) = nrm x * nrm y := by
  simp only [nrm, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul]
  ring

theorem mul_star_eq {R : Type*} [CommRing R] {a b : R} (x : ℍ[R, a, b]) : x * star x = algebraMap R ℍ[R, a, b] (nrm x) := by
  ext <;> simp [nrm, QuaternionAlgebra.algebraMap_eq] <;> ring

theorem nrm_rat {a b : F} (x : ℍ[F, a, b]) : nrm (rat x) = algebraMap F (AF F) (nrm x) := by
  simp [nrm, rat]

theorem one_mem_H0_weight_zero {a b : F} (ε : AF F) : (1 : DA F a b) ∈ H0 ε :=
  ⟨1, by simp [nrm], 1, by simp [nrm], by simp, by ext <;> simp [rat]⟩

end GlobalTheory.QSA
