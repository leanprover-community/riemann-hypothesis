module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Transported
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
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
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.S.Pv.BetaCut

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

def coefM {k r : ℕ} {H Wp Wq : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (v v' : H) (ξ : Wp) (ξ' : Wq)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Wq →L[ℂ] Wp :=
  (innerSL ℂ ξ').smulRight (⟪v, σ g v'⟫_ℂ • ξ)

def CoefInCC : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (h : ℝ) (m : ℕ) (A : ℝ),
    IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ → GapAtLeast ε lam h → ReciprocityTheory.ChartRestriction.DS.thrStar ε + m < h → A ≤ m →
    ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ v' ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
      (ξ : Wp) (ξ' : Wq), Formalism.FourierDecayAlt.B.InCC (k := k) (r := r) A 5 (coefM σ v v' ξ ξ')

def BetaInfCoefNZ : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq)
    (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (h : ℝ),
    IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ → GapAtLeast ε lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h →
    ∀ (v v' : H) (l : H → Wp) (l' : H → Wq) (ξ : Wp) (ξ' : Wq),
      v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ → v' ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ →
      Formalism.FourierDecayAlt.ThreeDimData.be D.z Formalism.QuantumDeterminants.cStd D.π σ D.μW D.μN v v = (innerSL ℂ (l v)).smulRight (l v) →
      Formalism.FourierDecayAlt.ThreeDimData.be D.z' Formalism.QuantumDeterminants.cStd D.π' σ D.μW' D.μN v' v' = (innerSL ℂ (l' v')).smulRight (l' v') →
      ⟪l v, ξ⟫_ℂ ≠ 0 → ⟪ξ', l' v'⟫_ℂ ≠ 0 →
      Formalism.FourierDecayAlt.B.betaInf D (coefM σ v v' ξ ξ') (coefM σ v v' ξ ξ') ≠ 0

end Formalism.MainNotions.S.Pv.BetaCut
