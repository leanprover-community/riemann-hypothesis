module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def RadMaxAt (B : Base F E) (M : Model σ X W) (om : Rep σ X W) : Prop :=
  ∀ β : M.Pol B.ψ B.emb →ₗ⋆[ℂ] M.Pol B.ψ B.emb →ₗ[ℂ] ℂ, (∀ x y, β x y = starRingEnd ℂ (β y x)) →
    (∀ γ ∈ Lines σ X, ∀ x y : M.Pol B.ψ B.emb,
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) x.1 y.1 → β y = 0) →
    (∀ δ ∈ Lines σ W, ∀ x x₁ y y₁ : M.Pol B.ψ B.emb, ActsD (evI F) (fun t => om (1, δ (Multiplicative.ofAdd t))) x.1 x₁.1 →
      ActsD (evI F) (fun t => om (1, δ (Multiplicative.ofAdd t))) y.1 y₁.1 → β x₁ y + β x y₁ = 0) →
    ∀ P : Submodule ℂ (M.Pol B.ψ B.emb), LinearMap.ker β ≤ P →
      (∀ δ ∈ Lines σ W, ∀ x ∈ P, ∀ y : M.Pol B.ψ B.emb,
        ActsD (evI F) (fun t => om (1, δ (Multiplicative.ofAdd t))) x.1 y.1 → y ∈ P) → P ≤ LinearMap.ker β ∨ P = ⊤

def RadMax : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    RadMaxAt B G.M om ∧ RadMaxAt B G.M' om'

end PositivityTheory.ThKF

end
