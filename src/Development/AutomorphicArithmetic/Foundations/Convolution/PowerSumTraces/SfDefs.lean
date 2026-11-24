module

public import GroundTheory.AutomorphicForms.SmoothRep
public import GroundTheory.AutomorphicForms.UnitaryRepresentations.IsInvariantIffCommuteStarProjection
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
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

open GroundTheory.Automorphic
open scoped InnerProductSpace

namespace UpperTheory.ConvolutionTheory.C.Sf

variable {G : Type} [Group G] [TopologicalSpace G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {S : Type} [AddCommGroup S] [Module ℂ S]

def fixU (π : UnitaryRep G H) (U : Subgroup G) : Submodule ℂ H where
  carrier := {v | ∀ u ∈ U, π u v = v}
  add_mem' {a b} ha hb u hu := by rw [map_add (f := _), ha u hu, hb u hu]
  zero_mem' u _ := map_zero _
  smul_mem' c v hv u hu := by rw [map_smul, hv u hu]

theorem mem_fixU {π : UnitaryRep G H} {U : Subgroup G} {v : H} : v ∈ fixU π U ↔ ∀ u ∈ U, π u v = v := Iff.rfl

theorem isClosed_fixU (π : UnitaryRep G H) (U : Subgroup G) : IsClosed (fixU π U : Set H) := by
  have : (fixU π U : Set H) = ⋂ u ∈ U, {v | π u v = v} := by
    ext v
    simp [mem_fixU]
  rw [this]
  exact isClosed_biInter fun u _ => isClosed_eq (π u).continuous continuous_id

structure Eqv (τ : Representation ℂ G S) (π : UnitaryRep G H) (D : Submodule ℂ H) (f : S →ₗ[ℂ] H) : Prop where
  mem : ∀ x, f x ∈ D
  map : ∀ g x, f (τ g x) = π g (f x)

def spanAll (τ : Representation ℂ G S) (π : UnitaryRep G H) (D : Submodule ℂ H) : Submodule ℂ H :=
  Submodule.span ℂ {y | ∃ f, Eqv τ π D f ∧ ∃ x, y = f x}

def spanFix (τ : Representation ℂ G S) (π : UnitaryRep G H) (D : Submodule ℂ H) (U : Subgroup G) : Submodule ℂ H :=
  Submodule.span ℂ {y | ∃ f, Eqv τ π D f ∧ ∃ x ∈ fixedVectors τ U, y = f x}

def IsOp [MeasurableSpace G] (π : UnitaryRep G H) (m : MeasureTheory.Measure G) (φ : G → ℂ) (T : H →L[ℂ] H) : Prop :=
  ∀ u v : H, ⟪u, T v⟫_ℂ = ∫ g, φ g * ⟪u, π g v⟫_ℂ ∂m

end UpperTheory.ConvolutionTheory.C.Sf
