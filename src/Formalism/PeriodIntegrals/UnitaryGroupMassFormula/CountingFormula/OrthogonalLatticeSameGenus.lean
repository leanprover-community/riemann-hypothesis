module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
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

open NumberField Module
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

open Formalism.HermitianLattices.Ext.L3

section Glue

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V1 : Type} [AddCommGroup V1] [Module K V1] [Module (𝓞 K) V1] [IsScalarTower (𝓞 K) K V1]

def wPerp (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) : Submodule K V1 := LinearMap.ker (h1 z)

def hPerp (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) : wPerp h1 z →ₗ⋆[K] wPerp h1 z →ₗ[K] K :=
  (h1.compl₂ (wPerp h1 z).subtype).comp (wPerp h1 z).subtype

def l0 (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (M : Submodule (𝓞 K) V1) : Submodule (𝓞 K) (wPerp h1 z) :=
  M.comap ((wPerp h1 z).subtype.restrictScalars (𝓞 K))

def IsGlueLat (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (M : Submodule (𝓞 K) V1) : Prop :=
  Submodule.IsLattice K M ∧ Formalism.HermitianLatticesTheory.IsUnimodular h1 M ∧ z ∈ M ∧
    ∀ c : K, c • z ∈ M → ∃ o : 𝓞 K, (o : K) = c

def hz (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) : Set (V1 ≃ₗ[K] V1) :=
  {σ | σ ∈ Formalism.HermitianLatticesTheory.isom h1 ∧ σ z = z}

def stabZ (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (M : Submodule (𝓞 K) V1) : Set (V1 ≃ₗ[K] V1) :=
  {σ | σ ∈ hz h1 z ∧ Formalism.HermitianLatticesTheory.gmap σ M = M}

def IsHzReps (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (s : Finset (Submodule (𝓞 K) V1)) : Prop :=
  (∀ M ∈ s, IsGlueLat h1 z M) ∧
    ∀ M, IsGlueLat h1 z M → ∃! M', M' ∈ s ∧ ∃ σ ∈ hz h1 z, Formalism.HermitianLatticesTheory.gmap σ M' = M

end Glue

def GlueHyp (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    {V1 : Type} [AddCommGroup V1] [Module K V1] [Module (𝓞 K) V1] [IsScalarTower (𝓞 K) K V1]
    (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (t : ℕ) : Prop :=
  Formalism.HermitianLatticesTheory.IsCMUnram K ∧ IsFixF K F ∧ h1.IsSymm ∧ h1 z z = -((t : ℕ) : K) ∧ 0 < t ∧
    IsTotPosDef (hPerp h1 z)

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
