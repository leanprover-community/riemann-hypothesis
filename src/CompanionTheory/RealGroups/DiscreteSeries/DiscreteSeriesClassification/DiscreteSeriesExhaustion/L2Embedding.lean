module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GoodPathReplicate
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SquareIntegrableInnerProduct
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Finset

namespace CompanionTheory.RgExh

open Formalism.REAL (GlRel IsUnitary KHighest IsWeight)
open CompanionTheory.D.LK (IsKMod LocFin IsMin)

variable {n : ℕ}

def L2Embedding (ε : Fin n → Bool) (X : GMod n) : Prop :=
  ∀ u : X.V, u ≠ 0 → ∃ c : X.V →ₗ[ℂ] ReciprocityTheory.ChartRestriction.DS.smD ε (ReciprocityTheory.ChartRestriction.DS.rreg ε),
    (∀ a b x, c (X.E a b x) = ReciprocityTheory.ChartRestriction.DS.smE ε (ReciprocityTheory.ChartRestriction.DS.rreg ε) a b (c x)) ∧ c u ≠ 0

def Decay : Prop :=
  ∀ n : ℕ, ∃ B : ℝ, ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (hK : IsKMod ε σ D E) (χ : Fin n → ℂ) (ss : List (Fin n)),
    Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ → Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ → Formalism.MainNotions.S.IsSqIntOn ε σ →
    HasChar ⟨D, E, hK.gl⟩ χ → GoodPath χ ss → FarLabels χ (pathEnd χ ss) B → L2Embedding ε (path ⟨D, E, hK.gl⟩ χ ss)

def IntWt (X : GMod n) : Prop := ∀ (μ : Fin n → ℝ) (x : X.V), x ≠ 0 → IsWeight X.E μ x → ∀ a, ∃ m : ℤ, μ a = m

def AlgDS (ε : Fin n → Bool) (X : GMod n) (s : Equiv.Perm (Fin n)) (mu : Fin n → ℝ) : Prop :=
  Formalism.QuantumDeterminants.IsHCParam mu ∧ (∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) ∧
    IsMin (ε ∘ s) (fun a b => X.E (s a) (s b)) mu ∧
    ∃ v : X.V, v ≠ 0 ∧ KHighest (ε ∘ s) (fun a b => X.E (s a) (s b)) (PI.UpqRep.lowK (ε ∘ s) mu) v

def FarReg : Prop :=
  ∀ (n : ℕ) (C δ : ℝ), 0 < δ → ∃ N₀ : ℝ, ∀ (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (χ : Fin n → ℂ) (N : ℝ), Nontrivial V → IsUnitary ε E →
    LocFin ε E → IntWt ⟨V, E, hE⟩ → ScalChar ⟨V, E, hE⟩ χ → N₀ ≤ N → (∀ a b, a ≠ b → δ * N ≤ |(χ a).re - (χ b).re|) →
    (∀ a, |(χ a).re| ≤ C * N ∧ |(χ a).im| ≤ C) → ∃ s mu, AlgDS ε ⟨V, E, hE⟩ s mu

end CompanionTheory.RgExh
