module

public import Formalism.LocalRingCardinality.PrincipalHermitianLattice
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions

open NumberField

def DV.Used (D : D7) (μ : D.what₂.Tup) : Prop :=
  μ = D.what₂.mu0 ∨ μ = D.what₂.muStar ∨ μ = D.what₂.muStar' ∨ ∃ w, μ = D.what₂.muAt w

structure AmbForm (D : D7) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    [FiniteDimensional ℂ EE] (S : RowSide D EE) where

  MtH : D.what₂.Tup → HLat D.what₂.LL

  jAmb : ∀ μ, (MtH μ).V →ₛₗ[D.what₂.embLL] S.Amb μ
  MtH_good : ∀ μ, DV.Used D μ → (MtH μ).Good
  jAmb_basis : ∀ μ, DV.Used D μ → LinearIndependent ℂ (fun i => jAmb μ ((MtH μ).b i)) ∧
    Submodule.span ℂ (Set.range (fun i => jAmb μ ((MtH μ).b i))) = ⊤

  jAmb_lat : ∀ μ, DV.Used D μ → ∀ x, x ∈ (MtH μ).L ↔ ∃ c : S.Amb μ → 𝓞 D.what₂.LL,
    jAmb μ x = ∑ v ∈ (S.Mtilde μ).gen, D.what₂.embLL ((c v : 𝓞 D.what₂.LL) : D.what₂.LL) • v

  jAmb_gen : ∀ μ, DV.Used D μ → ∀ v ∈ (S.Mtilde μ).gen, v ∈ Set.range (jAmb μ)

  jAmb_norm : ∀ μ, DV.Used D μ → ∀ x,
    Formalism.HermitianLatticesTheory.normAt (MtH μ).b (MtH μ).X (InfinitePlace.mk D.what₂.embLL) x = ‖jAmb μ x‖

end Formalism.BasicNotions

end
