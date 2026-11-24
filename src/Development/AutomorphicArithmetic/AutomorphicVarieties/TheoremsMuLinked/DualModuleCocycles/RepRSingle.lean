module

public import Mathlib.Algebra.DualNumber
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.Idempotents
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

noncomputable section

open Matrix UpperTheory.V.W

namespace UpperTheory.V.Th.Coc

variable {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ}


variable (X) in
abbrev bar (Z : Matrix (Fin n) (Fin n) O) : Matrix (Fin n) (Fin n) X := Z.map (algebraMap O X)

def repR {G : Type} [Group G] (x : R →ₐ[O] O) (ρ : G →* Matrix (Fin n) (Fin n) O) :
    MonoidAlgebra R G →+* Matrix (Fin n) (Fin n) O :=
  (GDet.repAlg ρ O).toRingHom.comp (MonoidAlgebra.mapRingHom G x.toRingHom)

theorem repR_single {G : Type} [Group G] (x : R →ₐ[O] O) (ρ : G →* Matrix (Fin n) (Fin n) O) (g : G) (a : R) :
    repR x ρ (MonoidAlgebra.single g a) = x a • ρ g := by
  simp [repR, GDet.repAlg, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.lift_single]

structure IsLift {E : Type} [Ring E] [Algebra R E] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ : E →+* Matrix (Fin n) (Fin n) O)
    (τ : E → R) (c : O) (d : E →+ Matrix (Fin n) (Fin n) X) : Prop where
  mul : ∀ a b, d (a * b) = d a * bar X (ρ b) + bar X (ρ a) * d b
  smul : ∀ (r : R) a, d (r • a) = x r • d a + (c • δ r) • bar X (ρ a)
  tr : ∀ a, (d a).trace = c • δ (τ a)

structure IsTrGMA {E : Type} [Ring E] [Algebra R E] (τ : E →ₗ[R] R) (e : Fin n → E) : Prop where
  comm : ∀ a b, τ (a * b) = τ (b * a)
  idem : CompleteOrthogonalIdempotents e
  corner : ∀ i a, e i * a * e i = τ (e i * a) • e i
  one : ∀ i, τ (e i) = 1

def dualM (A B : Matrix (Fin n) (Fin n) X) : Matrix (Fin n) (Fin n) (DualNumber X) :=
  Matrix.of fun i j => TrivSqZeroExt.inl (A i j) + TrivSqZeroExt.inr (B i j)

def kEl {A : Type} [CommRing A] (u : Matrix (Fin n) (Fin n) A) (α : Fin n → A) (i : Fin n) : Matrix (Fin n) (Fin n) A :=
  Polynomial.aeval u (∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (α j)))

def kS {A : Type} [CommRing A] (u : Matrix (Fin n) (Fin n) A) (α : Fin n → A) : Matrix (Fin n) (Fin n) A :=
  Matrix.of fun a b => kEl u α a a b

def kT {A : Type} [CommRing A] (u : Matrix (Fin n) (Fin n) A) (α : Fin n → A) : Matrix (Fin n) (Fin n) A :=
  Matrix.of fun a b => kEl u α b a b

end UpperTheory.V.Th.Coc
