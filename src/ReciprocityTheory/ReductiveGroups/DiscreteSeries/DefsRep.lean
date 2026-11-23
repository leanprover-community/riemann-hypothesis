module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def Jm (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a => if ε a then 1 else -1

def inUJ (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  gᴴ * Jm ε * g = Jm ε

def UJset (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) := {g | inUJ ε g}

def Kset (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {g | g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Jm ε = Jm ε * g}

def inG (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Xᴴ * Jm ε + Jm ε * X = 0

def inK (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  inG ε X ∧ X * Jm ε = Jm ε * X

def inP (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  inG ε X ∧ X * Jm ε = -(Jm ε * X)

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsURepOn (G : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  (σ 1 = 1 ∧ ∀ a ∈ G, ∀ b ∈ G, σ (a * b) = (σ a).comp (σ b)) ∧
    (∀ g ∈ G, ∀ v : H, ‖σ g v‖ = ‖v‖) ∧ ∀ v : H, ContinuousOn (fun g => σ g v) G

def actM {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (X : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ M :=
  ∑ a, ∑ b, X a b • E a b

structure IsDerivedOn (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D) : Prop where
  glRep : IsGlRep E
  kStable : ∀ k ∈ Kset ε, ∀ v ∈ D, σ k v ∈ D
  deriv : ∀ X, inG ε X → ∀ v : D,
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)) ((actM E X v : D) : H) 0

end Rep

end ReciprocityTheory.ChartRestriction.DS
